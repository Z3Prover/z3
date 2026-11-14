############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Reconstruct a supported native Boolean, QF_LRA, or QF_UF refutation in Lean.
############################################
"""Check native Boolean, linear real arithmetic, and uninterpreted-function refutations in Lean.

Boolean steps become explicit Lean proof terms. Arithmetic atoms are encoded
over Rat, and theory lemmas and arithmetic rewrites are discharged by Lean's
grind tactic after a Python pre-check of the recorded Farkas combination.
The uninterpreted sorts become one type variable with constants, functions, and
predicates over argument lists; grind's congruence closure proves euf lemmas.
"""

import argparse
from collections import Counter, deque
from dataclasses import dataclass, field
from fractions import Fraction
import functools
import hashlib
import itertools
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import z3

from proof_certificate import (
    RECOGNIZER_KINDS, SET_OPERATORS, ProofExportError, _rounded, array_leaf_sorts, array_sort_name,
    bound_combination_refutes,
    enumeration_constructors, expand_polynomial, integer_tightened, is_carrier_sort, is_enumeration_sort,
    linear_combination_refutes, numeral_value, parse_assertions, polynomial_refutation, pseudo_boolean_parameters,
    query_snapshot, MAP_ARITY, map_parameters,
)


class ReconstructionError(Exception):
    """A certificate is malformed, unsupported, or does not prove this input."""


_CHECK_LEAN = Path(__file__).resolve().parents[2] / "scripts" / "check_lean.sh"
_BOOL_NAMES = {
    z3.Z3_OP_TRUE: "true", z3.Z3_OP_FALSE: "false", z3.Z3_OP_NOT: "not",
    z3.Z3_OP_AND: "and", z3.Z3_OP_OR: "or", z3.Z3_OP_IMPLIES: "=>",
    z3.Z3_OP_XOR: "xor", z3.Z3_OP_EQ: "=", z3.Z3_OP_IFF: "iff",
    z3.Z3_OP_DISTINCT: "distinct", z3.Z3_OP_ITE: "if",
}
_FIXED_ARITY = {
    z3.Z3_OP_TRUE: 0, z3.Z3_OP_FALSE: 0, z3.Z3_OP_UNINTERPRETED: 0,
    z3.Z3_OP_NOT: 1, z3.Z3_OP_IMPLIES: 2, z3.Z3_OP_XOR: 2,
    z3.Z3_OP_EQ: 2, z3.Z3_OP_IFF: 2, z3.Z3_OP_ITE: 3,
}
_ARITH_PREDICATE_NAMES = {z3.Z3_OP_LE: "<=", z3.Z3_OP_GE: ">=", z3.Z3_OP_LT: "<", z3.Z3_OP_GT: ">"}
# Pseudo-Boolean constraints (propositional certificates only): name, the
# relation between the weighted count of the true literals and the bound,
# and whether the declaration carries a coefficient per argument (at-most and
# at-least weigh every literal 1). A literal l counts as its 0/1 value, the
# classical (if l then 1 else 0) over Int (_pseudo_boolean_body).
_PSEUDO_BOOLEAN = {
    z3.Z3_OP_PB_AT_MOST: ("at-most", "<=", False), z3.Z3_OP_PB_AT_LEAST: ("at-least", ">=", False),
    z3.Z3_OP_PB_LE: ("pble", "<=", True), z3.Z3_OP_PB_GE: ("pbge", ">=", True), z3.Z3_OP_PB_EQ: ("pbeq", "=", True),
}
_REAL_NAMES = {z3.Z3_OP_ADD: "+", z3.Z3_OP_SUB: "-", z3.Z3_OP_UMINUS: "-", z3.Z3_OP_MUL: "*", z3.Z3_OP_DIV: "/"}
_REAL_ARITY = {z3.Z3_OP_UNINTERPRETED: 0, z3.Z3_OP_ANUM: 0, z3.Z3_OP_UMINUS: 1, z3.Z3_OP_DIV: 2}
# The integer operators, Int certificates only: div and mod by a nonzero
# numeral are Lean's Euclidean Int division and remainder (/ and %, which
# agree with SMT-LIB's away from zero; a zero divisor is rejected, see
# _integer_divisor), abs is the ite SMT-LIB defines it as. rem, a Z3
# extension, is Z3's definition (ite (>= k 0) (mod t k) (- (mod t k)))
# evaluated at its constant divisor k: t % k for a positive k, 0 - t % k for
# a negative one (the negation as a difference, like every Int negation and
# the negative branch of abs, see _negation; a div by a negative constant d
# is 0 - t / (0 - d), see _negative_quotient). All four are
# opaque atoms of the linear forms; omega reads / and % by a positive
# numeral and grind proves the axioms of a negative divisor. abs is also a
# Real operator (_NUMERIC_KINDS): SMT-LIB defines it on Int only, but Z3
# accepts it over Real with the same definition, (ite (>= t 0) t (- t)), and
# its rewriter replaces it by that ite before solving.
_INT_NAMES = {z3.Z3_OP_IDIV: "div", z3.Z3_OP_MOD: "mod", z3.Z3_OP_REM: "rem", z3.Z3_OP_ABS: "abs"}
_INT_ARITY = {z3.Z3_OP_IDIV: 2, z3.Z3_OP_MOD: 2, z3.Z3_OP_REM: 2, z3.Z3_OP_ABS: 1}
# The integer operators taking a divisor, a nonzero numeral (_integer_divisor).
_DIVISION_KINDS = (z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM)
_NUMERIC_KINDS = {z3.Z3_OP_ABS}
# An ite is the one arithmetic or uninterpreted-sort term with a Boolean
# argument; Lean's ite needs a decidability instance, which the classical one
# provides. Every theory slice already depends on the standard axioms.
_REAL_DOMAIN_PREDICATES = _ARITH_PREDICATE_NAMES.keys() | {z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT}
# cut: the integer solver's Gomory cuts and gcd conflicts. The exporter keeps
# no coefficients for it (the log's unit weights certify nothing about the
# rounding), nor for an Int farkas or bound whose coefficients did not
# re-derive the lemma; such th-lemmas are shape-checked and proved by Lean
# alone, in Int certificates only.
_COEFFICIENT_HINTS = ("farkas", "bound", "implied-eq", "cut")
# triangle-eq: the legacy core's axioms tying a Real equality to its two
# inequalities, proved by grind like every other theory tautology. arith: the
# sat.smt arithmetic solver's own axioms (the div, mod, and rem definitions), a
# clause of linear arithmetic atoms without coefficients, proved by Lean.
# pb: theory_pb's propagations, conflicts, and constraint axioms, proved over
# the 0/1 values of the variables (_pseudo_boolean_lemma). array: the sat.smt
# array solver's axiom instances (store, select over store, extensionality), a
# clause of equalities proved by grind with the array facts (_array_helpers).
# datatype: the case splits and constructor clashes of the datatype solver over
# an enumeration, a clause of equalities between its terms and constructors,
# proved by grind from the enumeration fields (_enumeration_helpers).
# nla: a lemma of the nonlinear solver, a clause of bounds and equalities over
# Int terms with products whose literals have a polynomial refutation, found
# again here and proved from the products of the bounds (_product_combination).
_HINTS = _COEFFICIENT_HINTS + ("euf", "tseitin", "smt", "cnf", "triangle-eq", "arith", "pb", "array", "datatype",
                               "nla")
_FRAGMENTS = ("propositional", "qf_lra", "qf_lia", "qf_lira", "qf_uf", "qf_uflra", "qf_uflia", "qf_uflira")
# The arithmetic sorts and their Lean carriers: Real variables are valued in
# Rat (see the exporter README for the soundness argument), Int variables in
# Int, where omega decides the linear integer lemmas (see _grind_lemma).
_ARITH_SORTS = ("Real", "Int")
_NUMBER_TYPES = {"Real": "Rat", "Int": "Int"}
# The arithmetic of a qf_lira certificate: Int and Real variables side by
# side, each sort with its own valuation (_ivars into Int, _vars into Rat),
# and the conversions between them: to_real, Lean's Int.cast into Rat,
# to_int, Rat.floor, and is_int, a Real term equal to the cast of its floor.
# Whatever depends on the sort (numerals, rounding, the theory tactic) is
# read off the node; a theory lemma over atoms of both sorts is rejected
# unless it reaches a conversion (_lemma_numeric).
_MIXED = "Int and Real"
# The arithmetic class of a qf_lira theory step reaching a conversion (_lemma_numeric).
_CAST = "Int and Real through a conversion"
# The fragments mixing arithmetic with uninterpreted symbols, by arithmetic sort.
_MIXED_FRAGMENTS = {"Real": "qf_uflra", "Int": "qf_uflia", _MIXED: "qf_uflira"}
# Refutations with more proof steps than this are split into separately
# checked lemmas, none nesting more than _OUTLINE_CHUNK_STEPS steps: one
# nested term elaborates superlinearly and exhausts the default heartbeat
# budget between 1,000 and 2,000 steps.
_OUTLINE_PROOF_STEPS = 500
_OUTLINE_CHUNK_STEPS = 500
# A step with more premises or clause literals than this counts as that many
# steps of its chunk (_outline_weight).
_OUTLINE_WIDE_STEP = 64
# A step under hypotheses used by one other step is bound inside it
# (_step_blocks), at most this many such steps deep.
_NESTED_STEP_DEPTH = 32
# and-elim projects an operand by field notation, one `.2` per operand before
# it, so eliminating every operand of a wide conjunction is quadratic: 250
# projections out of a 600-operand conjunction (94,000 `.2`s in one outlined
# lemma) exhausted its heartbeats. The rest of the conjunction is let-bound
# once every _AND_ELIM_STRIDE operands (_tail_lets) and a projection starts
# from the nearest such tail.
_AND_ELIM_STRIDE = 32
_NORMALIZED_REWRITE_ATOMS = 16
# Condition leaves (Boolean variables and linear atoms) an ite term of a
# normalized rewrite may have to be keyed by its value table, which has one
# row per assignment (_ite_table); the spider and carpark QF_LRA rewrites
# have at most four.
_ITE_TABLE_LEAVES = 8
# And the nodes of its branches and conditions, which bounds the cost of a
# row and the depth of evaluating a condition.
_ITE_TABLE_NODES = 200
# Heartbeats (Lean's unit, thousands of small allocations) of an Int lattice
# lemma (a cut, or a farkas or bound without coefficients) over its atoms
# generalized, where grind's cutsat module decides the goal (see
# _opaque_tactic); the other lemmas keep the million.
_LATTICE_LEMMA_HEARTBEATS = 2000000
# Premises plus clause literals from which an Int farkas or bound lemma is
# proved by its combination (_farkas_combination) rather than left to omega:
# with fewer bounds omega finds the combination quickly, and its proof costs
# Lean less memory than the combination's (about 1 MB against 3 MB per
# lemma: the wide division seed's Farkas lemmas, 800 of them, mostly of two
# literals, peaked at 8.5 GB through the combination against 7.7 GB through
# omega, and its 121 of ten bounds or more at 8.1 GB). The conflicts omega
# could not finish had 21 (QF_LIA cut_lemmas).
_FARKAS_COMBINATION_BOUNDS = 16
# The magnitude one of those coefficients must reach as well: omega proved
# the wide division seed's 59 lemmas of 16 to 26 bounds, coefficients at
# most 780, quickly, and their combinations alone raised that certificate's
# Lean peak by 0.2 GB, close to the 8 GB cap; the conflicts omega could
# not finish had coefficients of seven and eight digits.
_FARKAS_COMBINATION_COEFFICIENT = 10000
# Or the atoms one of those bounds must reach (a dense bound): omega took
# over a minute, or six gigabytes, on 9 of the 25 Farkas lemmas of 20 and 21
# bounds over twenty variables, coefficients below 10,000, of QF_LIA
# cut_lemma_02_002, whose bounds span 19 atoms each; the wide division
# seed's bounds span at most four.
_FARKAS_COMBINATION_ATOMS = 8
# The most factors whose signs the proof of a step over Int products splits
# on (_sign_cases): three cases each, the factors after a zero one unsplit.
# A product of five factors takes 31 splits and 63 leaves (0.6 s of Lean).
_SIGN_SPLIT_FACTORS = 5
# Resource limits of the searches z3 makes for the split of an Int lattice
# lemma (_split_certificate), first with the split's coefficients bounded by
# one, then unbounded (_SPLIT_MAGNITUDES). Bounded, each of the 188
# lattice lemmas of QF_LIA cut_lemma_02_002 has one within 3 million (4 s of
# z3 for all of them), so the bounded limit leaves rlimit accounting on
# other platforms and builds a margin of six; a bounded search that fails
# costs at most about 3 s. Unbounded, two of them needed 50 million and
# over 400 million (a minute of z3).
_SPLIT_BOUNDED_RLIMIT = 20000000
_SPLIT_RLIMIT = 5000000
_SPLIT_MAGNITUDES = (1, None)
# The formulas a normalized rewrite's propositional lemma states over its
# atoms (Boolean = is checked separately: its arguments must be formulas).
_NORMALIZED_CONNECTIVES = (z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_NOT, z3.Z3_OP_IMPLIES, z3.Z3_OP_IFF,
                           z3.Z3_OP_XOR, z3.Z3_OP_ITE, z3.Z3_OP_TRUE, z3.Z3_OP_FALSE)
# Propagation steps and atom splits a propositional rewrite's direct proof may
# take, and characters its `have` lines may render (the `refine` and bullet
# lines are not counted), before the truth table is used instead (see
# _PropositionalProver). The proof is a tactic script, which Lean elaborates
# in time about linear in its steps (a nested term was quadratic): the 1.1 MB
# cnf lemma of a 13,000-node QF_IDL circuit checks in under a minute, while
# a parity rewrite over seven atoms renders 2.8 MB and exceeds Lean's
# heartbeat limit.
_STRUCTURAL_REWRITE_STEPS = 20000
_STRUCTURAL_REWRITE_CHARS = 1000000
# Steps and characters each link between equivalent structures may use on
# top of those limits (see _PropositionalProver._prove_links), so a rewrite's
# budget grows with the structures it relates. Linking the 481 regrouped
# gates of a QF_LRA time-triggered startup rewrite (tta_startup
# simple_startup_15nodes) took 22,000 steps and 960,000 characters, 46 and
# 2,000 per link, and left nothing for the search over the two sides. The
# allowance is at most the limits themselves, so a rewrite's proof stays
# within twice them: uncapped, 1,641 links of a 40-node rewrite of the same
# shape rendered over 3 MB, which ran Lean out of memory where grind alone
# verifies.
_LINK_STEPS = 100
_LINK_CHARS = 5000
# The limits of a sweep (_PropositionalProver.sweep). The steps and characters
# the search of one link may take: a link is proved over the few gates between
# its ends and the links below them (the 16,400 links of the three RTCL
# circuits take at most 15,000 characters each). How many times the operands
# of the canonical gates a link's search meets are tied in turn, at first and
# when that fails, and how many times the refutation of the clause may open
# the structures it meets (the RTCL circuits take one). The characters of
# all the declarations of the sweeps of a file: ckt_PROP3_tf_30 takes 12
# million, in a 19 MB file that Lean checks in 56 s at 7.1 GB, under the
# 8 GB of check_lean.sh. A sweep stops when its canonical gates, the links
# it has proved, and the searches that failed have written more than what
# the earlier sweeps of the file left of that (ckt_PROP3_tf_30 counts 11.4
# million), and a longer sweep is not written. The members of all the
# and/or classes of a sweep: n nested conjunctions have classes of 2 to n
# members and as many canonical gates of that many operands, each a parent
# of its operands in every search (ckt_PROP3_tf_30 has 21 thousand members
# and sweeps in 1.4 s; two forms of a 400-deep conjunction have 81
# thousand, 1.4 s and 15 MB; the thousand nested ands of QF_IDL
# FISCHER6-4-ninc have 2 million, and their sweep did not end in 1,700 s).
# A wider formula is not swept.
_SWEEP_LINK_STEPS = 1000
_SWEEP_LINK_CHARS = 50000
_SWEEP_ROUNDS = (1, 3)
_SWEEP_OPENINGS = 4
_SWEEP_CHARS = 16000000
_SWEEP_MEMBERS = 200000
# Resource limit of z3's unsat core over a cnf lemma's propositional
# abstraction (_relevant_structures), which steers the prover when its own
# search gives up: the 5,649 gates of the QF_IDL plan-21 cnf lemma take
# 0.4 million (a quarter of a second).
_RELEVANCE_RLIMIT = 10000000
# Theory clauses _theory_clauses may add to a cnf lemma whose propositional
# abstraction does not refute it, the resource limit of each of its z3 checks,
# and the factor of the prover's limits for the search over the clauses. The
# cnf lemma of QF_LRA tta_startup simple_startup_11nodes takes 45 clauses
# over its leaves, found in under two seconds, and the search over them 36,000
# steps and 3.3 million characters (0.2 s), of which the 0.45 MB proof is kept:
# that is the last attempt before the fallback, a grind over the unfolded
# clause (227 ites) that runs out of heartbeats.
_THEORY_CLAUSES = 256
_THEORY_CLAUSE_RLIMIT = 5000000
_THEORY_CLAUSE_BUDGET = 10
# Characters of Lean text above which the file is elaborated one declaration
# at a time (Elab.async false, an elaboration schedule, not a trust setting).
# Elaborating declarations in parallel tasks keeps far more memory alive:
# z3test's NEQ004_size4 (21 MB) peaks above 10 GB in parallel and at 7.1 GB
# serially, against the 8 GB `--memory` cap of check_lean.sh, at the price
# of three times the wall time (about 100 s against 34 s). QF_LIA
# cut_lemma_02_002 (6.5 MB, 294 split and combination proofs of lattice and
# Farkas lemmas over twenty variables) exhausts the cap in parallel and
# peaks at 6.7 GB serially. No other test file exceeds 4 MB.
_SERIAL_ELABORATION_CHARS = 5000000
_RESERVED_SORTS = ("Bool", "Real", "Int", "Proof")
# The uninterpreted sorts are one type variable; constants, functions, and
# predicates are indexed families over argument lists, so one signature serves
# every arity and every sort. Quantifying over all such interpretations covers
# every model: a many-sorted model is one instance with the disjoint union of
# its carriers as _m.U, since every ground term keeps its sort and equality is
# only ever stated between terms of one sort (the certificate keeps the sort
# names, and the proof graph is checked to be well-sorted before rendering).
# A Boolean argument of a function or predicate is injected into _m.U by the
# quantified map _m.bool, so Bool is treated as one more sort: a model's Bool
# carrier joins the disjoint union and _m.bool picks its two values. Nothing
# asserts that _m.bool True and _m.bool False differ, and nothing needs to: euf
# lemmas only use the congruence p = q -> _m.bool p = _m.bool q.
# The carrier and the maps are the fields of one structure, Interpretation,
# declared in each file and quantified as the one argument _m (the carrier
# _m.U, the families _m.elems, _m.funs, _m.preds): every definition, lemma,
# and proof step takes it and every reference applies it, and one argument in
# place of five to seven cut z3test's NEQ004_size4 (13,700 declarations, elaborated
# serially) from 9.6 GB of Lean memory to 7.1 GB.
_UF_FIELDS = (("U", "Type"), ("elems", "Nat -> U"), ("funs", "Nat -> List U -> U"),
              ("preds", "Nat -> List U -> Prop"), ("bool", "Prop -> U"))
_UF_BINDERS = " (_m : Interpretation)"
_UF_ARGUMENTS = " _m"
# QF_UFLRA: the Rat valuation of the Real variables next to the carrier. A
# Real argument of a function or predicate is injected into _m.U by _m.real, as a
# Boolean one is by _m.bool (Real joins the disjoint union as one more carrier),
# and a function with a Real result is one more indexed family _m.rfuns whose
# applications are the opaque atoms of the linear forms, as in Z3's arithmetic
# solver. Nothing states that _m.real is injective and nothing needs it: euf
# lemmas only use the congruence x = y -> _m.real x = _m.real y. QF_UFLIA is the
# same encoding over Int, with the injection _m.int and the family _m.ifuns. The
# valuation stays a parameter of its own, as in QF_LRA and QF_LIA. QF_UFLIRA
# has both valuations, as qf_lira, and both pairs of fields: each numeric
# argument is injected and each function result valued by the fields of its
# own sort.
_NUMERIC_FIELDS = {"Real": (("real", "Rat -> U"), ("rfuns", "Nat -> List U -> Rat")),
                   "Int": (("int", "Int -> U"), ("ifuns", "Nat -> List U -> Int"))}
_NUMERIC_FIELDS[_MIXED] = _NUMERIC_FIELDS["Real"] + _NUMERIC_FIELDS["Int"]
# QF_AX: an array from one uninterpreted sort to another, (Array I E), is a
# function _m.U -> _m.U, the array constants the family _m.arrs. A model's
# array a : I -> E is the function agreeing with a on I and constant
# elsewhere: that embedding is injective and commutes with select and store
# at indices of I, so every model of the input is an instance. select is
# _select (application, kept as a binary function so grind's congruence
# closure compares reads of different arrays), store is _store, the
# classical update at one index, and the array solver's extensionality
# witness (_ array-ext 0) is _array_diff, an index where two arrays differ
# when they do (Classical.epsilon; _m.nonempty holds in every model, whose
# carriers are nonempty). Nothing here is assumed: _store_apply,
# _array_ext, _store_store, and _store_select are theorems. Array terms stay
# folded in the lemmas (see _definition_names and _array_helpers). An Int or
# Real index or element sort is Int or Rat itself (QF_ALIA, QF_AUFLIA), so a
# read of an Int array is an Int term, an atom of the linear forms like an
# application, and an index any Int term; each Lean array type has a family
# of its own (_array_family), and an extensionality witness over Int or Rat
# indices is chosen with the type's own inhabitant (_nonempty). Functions into
# an array sort are one more family per Lean array type (_array_functions).
# A Bool element sort is Prop (Prop : Type, so the definitions apply as they
# are): a set (Array I Bool) is a predicate I -> Prop, true exactly at the
# model's members in I, a read is a formula, and a stored value a formula.
# A Bool index sort is Prop too: an array over Bool is a function Prop -> E,
# into which a model's array a embeds as fun p => a (decide p) (injective,
# and commuting with select and store since equal propositions are equal,
# propext); an index and the extensionality witness are formulas, the
# witness chosen with True. A constant array over Bool indices is the
# constant function on Prop, which is what a model's embeds as; default
# values over Bool indices are rejected like those over uninterpreted sorts
# (_UNBOUNDED).
# Nested arrays: an index or element sort that is an array is that array's
# Lean function type, (Array Int (Array Int Int)) is Int -> (Int -> Int).
# A model embeds its inner arrays first (injectively, commuting with select
# and store), then each outer array as the function agreeing with it on the
# embedded indices and one fixed value elsewhere (so store, at an embedded
# index, and ite commute outside the image too, and two outer arrays that
# differ do so at an embedded index); a constant array is the constant
# function, which a model's is only where the embedding of the indices is
# onto, so constant arrays over array indices are rejected (_declaration).
# A pointwise connective
# does not commute with that embedding outside the image (not of the fixed
# value is another value), so maps and set operators over sets indexed by
# arrays are rejected (_declaration, proof_certificate's map_parameters);
# maps over rows of nested arrays (a set Int -> Prop read from a row of an
# Int -> (Int -> Prop)) are over Int indices. An uninterpreted index sort is
# in the same position whenever _m.U holds more than that sort, so the index
# sort of a map, a set operator, a subset, or a constant array is then a
# Lean type of its own, _m.S0, _m.S1, ..., over which the arrays are
# functions on exactly the model's indices (_index_sorts). A read of a row
# and an extensionality
# witness over array indices are array terms that lemmas unfold
# (_folded_array); the witness is chosen with a constant function (_nonempty).
_ARRAY_TYPE_CODES = {"_m.U": "u", "Int": "i", "Rat": "r", "Prop": "b"}
_NONEMPTY_FIELDS = (("nonempty", "Nonempty U"),)
_ARRAY_DEFINITIONS = """
def _select {I E : Type} (a : I -> E) (i : I) : E := a i

noncomputable def _store {I E : Type} (a : I -> E) (i : I) (v : E) : I -> E :=
  fun _j => @ite E (_j = i) (Classical.propDecidable _) v (a _j)

private theorem _store_apply {I E : Type} (a : I -> E) (i : I) (v : E) (j : I) :
    _select (_store a i v) j = @ite E (j = i) (Classical.propDecidable _) v (_select a j) := rfl

noncomputable def _array_diff {I E : Type} (h : Nonempty I) (a b : I -> E) : I :=
  @Classical.epsilon I h (fun _j => Not (a _j = b _j))

private theorem _array_ext {I E : Type} (h : Nonempty I) (a b : I -> E) :
    a = b \\/ Not (_select a (_array_diff h a b) = _select b (_array_diff h a b)) := by
  by_cases _e : Exists (fun _j => Not (a _j = b _j))
  . exact Or.inr (Classical.epsilon_spec _e)
  . exact Or.inl (funext (fun _j => Classical.byContradiction (fun _n => _e (Exists.intro _j _n))))

private theorem _array_diff_comm {I E : Type} (h : Nonempty I) (a b : I -> E) :
    _array_diff h a b = _array_diff h b a := by
  have _p : (fun _j => Not (a _j = b _j)) = (fun _j => Not (b _j = a _j)) :=
    funext (fun _j => propext (Iff.intro (fun _n _e => _n _e.symm) (fun _n _e => _n _e.symm)))
  exact congrArg (@Classical.epsilon I h) _p

private theorem _store_store {I E : Type} (a : I -> E) (i : I) (v w : E) :
    _store (_store a i v) i w = _store a i w := by
  funext _j
  by_cases _h : _j = i <;> simp [_store, _h]

private theorem _store_select {I E : Type} (a : I -> E) (i : I) : _store a i (_select a i) = a := by
  funext _j
  by_cases _h : _j = i <;> simp [_store, _select, _h]
""".strip("\n").split("\n")
# Arrays of an enumeration, (Array I Color): every read of an array constant
# or of a function into such arrays is one of the constructors (the fields
# enum_acases_i and enum_afcases_j, _enumeration_fields), and a read of a
# store or of an ite over arrays, or an ite of values, is one if what it
# may evaluate to is (a property P of the value: _cases_store, _cases_ite).
# _enumeration_helpers proves the cases of each read a lemma reaches with
# them, walking the read's array down to array constants and applications.
_ENUMERATION_ARRAY_DEFINITIONS = """
private theorem _cases_store {I E : Type} (P : E -> Prop) (a : I -> E) (i : I) (v : E) (j : I)
    (ha : P (_select a j)) (hv : P v) : P (_select (_store a i v) j) := by
  rw [_store_apply]
  split <;> assumption

private theorem _cases_ite {E : Type} (P : E -> Prop) (c : Prop) (h : Decidable c) (x y : E)
    (hx : P x) (hy : P y) : P (@ite E c h x y) := by
  split <;> assumption
""".strip("\n").split("\n")
# Constant arrays of an enumeration, ((as const (Array Int Color)) v): a read
# of one is v, and so is its default value; the default value of a store is
# the stored-into array's (_default_const, _default_store). So both are
# constructors if v is, and the default value of a store or an ite of arrays
# is one if those of the arrays below it are. The default value of an array
# constant or a function's array value has no such proof (_default of an
# array that is not constant almost everywhere is an arbitrary value), so
# _read_cases gives none for it. Stated after _CONSTANT_ARRAY_DEFINITIONS.
_ENUMERATION_CONSTANT_DEFINITIONS = """
private theorem _cases_const {I E : Type} (P : E -> Prop) (v : E) (j : I) (hv : P v) :
    P (_select (_const_array I v) j) := hv
""".strip("\n").split("\n")
# Not stated when the default values are read at a generic index
# (_GENERIC_DEFAULT_DEFINITIONS); _read_cases gives no proof for them then.
_ENUMERATION_DEFAULT_DEFINITIONS = """
private theorem _cases_default_const {I E : Type} (P : E -> Prop)
    (h : forall l : List I, Exists (fun x : I => Not (List.Mem x l))) (v : E) (hv : P v) :
    P (_default h (_const_array I v)) := by
  rw [_default_const]
  exact hv

private theorem _cases_default_store {I E : Type} (P : E -> Prop)
    (h : forall l : List I, Exists (fun x : I => Not (List.Mem x l))) (a : I -> E) (i : I) (v : E)
    (ha : P (_default h a)) : P (_default h (_store a i v)) := by
  rw [_default_store]
  exact ha
""".strip("\n").split("\n")
# A constant array ((as const (Array I E)) v) is the constant function
# _const_array, over Int, Real, and Bool indices and over an uninterpreted
# index sort, which is then exactly the model's (_index_sorts). The array
# solver relates constant arrays over Int and Real indices
# to others through their default value (default a), the value an array takes
# at all but finitely many indices: (default (const v)) = v and (default
# (store a i v)) = (default a). _default is a function on all of I -> E with
# both properties (_default_const, _default_store, theorems over any index
# type with no finite exhaustive list, _int_unbounded and _rat_unbounded): the
# value taken outside some finite list if there is one, which is unique then,
# and otherwise one value that a store does not change (Classical.choice of a
# Nonempty proof, and proofs are irrelevant). Over a finite index sort no such
# function exists (a store at every index turns one constant array into
# another), so the exporter and the reconstructor admit default values over
# Int and Real indices only (_UNBOUNDED); over the other index sorts two
# constant arrays are compared at one index instead (_index_witness), and a
# refutation that needs the default value of a store there is rejected. A
# constant array is a store of its value at any index
# (_const_store_self: for maps of stores next to constant arrays, and for
# Z3's rewriter, which folds (store (const c) i c) into (const c)), and
# equal to a store into it exactly when the stored value is its own
# (_const_eq_store, _store_eq_const: the rewriter decides such equalities).
# A store chain over a constant array takes the constant's value off the
# stored indices (_store_off, see _constant_chain_extensionality).
_CONSTANT_ARRAY_DEFINITIONS = """
def _const_array (I : Type) {E : Type} (v : E) : I -> E := fun _ => v

private theorem _select_const {I E : Type} (v : E) (i : I) : _select (_const_array I v) i = v := rfl

private theorem _const_store_self {I E : Type} (c : E) (i : I) : _const_array I c = _store (_const_array I c) i c := by
  funext _j
  by_cases _h : _j = i <;> simp [_const_array, _store, _h]

private theorem _const_eq_store {I E : Type} (c v : E) (i : I) :
    (_const_array I c = _store (_const_array I c) i v) = (c = v) := by
  apply propext
  constructor
  . intro _h
    have _hi := congrArg (fun _a => _a i) _h
    simp only [_const_array, _store, ite_true] at _hi
    exact _hi
  . intro _h
    rw [← _h]
    exact _const_store_self c i

private theorem _store_eq_const {I E : Type} (c v : E) (i : I) :
    (_store (_const_array I c) i v = _const_array I c) = (c = v) :=
  propext (Iff.intro (fun _h => (Iff.of_eq (_const_eq_store c v i)).mp _h.symm)
    (fun _h => ((Iff.of_eq (_const_eq_store c v i)).mpr _h).symm))

private theorem _store_off {I E : Type} (a : I -> E) (i : I) (v : E) (j : I) (h : Not (j = i)) :
    _store a i v j = a j := by
  simp [_store, h]
""".strip("\n").split("\n")
# The proofs that no finite list exhausts the index type, one per index sort
# of _UNBOUNDED; a file proves those of its array sorts' indices
# (_constant_array_definitions).
_UNBOUNDED_THEOREMS = {"Int": """
private theorem _int_unbounded : forall l : List Int, Exists (fun x : Int => Not (List.Mem x l)) := by
  intro l
  have _b : Exists (fun b : Int => forall y : Int, List.Mem y l -> y < b) := by
    induction l with
    | nil => exact Exists.intro 0 (fun _ h => nomatch h)
    | cons a t ih =>
      obtain ⟨b, hb⟩ := ih
      refine Exists.intro (max (a + 1) b) (fun y h => ?_)
      cases h with
      | head => omega
      | tail _ h => have := hb y h; omega
  obtain ⟨b, hb⟩ := _b
  exact Exists.intro b (fun h => Int.lt_irrefl b (hb b h))
""".strip("\n").split("\n"), "Real": """
private theorem _rat_unbounded : forall l : List Rat, Exists (fun x : Rat => Not (List.Mem x l)) := by
  intro l
  have _b : Exists (fun b : Rat => forall y : Rat, List.Mem y l -> y < b) := by
    induction l with
    | nil => exact Exists.intro 0 (fun _ h => nomatch h)
    | cons a t ih =>
      obtain ⟨b, hb⟩ := ih
      refine Exists.intro (max (a + 1) b) (fun y h => ?_)
      cases h with
      | head => grind
      | tail _ h => have := hb y h; grind
  obtain ⟨b, hb⟩ := _b
  exact Exists.intro b (fun h => Rat.lt_irrefl (hb b h))
""".strip("\n").split("\n")}
_DEFAULT_DEFINITIONS = """
noncomputable def _default {I E : Type} (h : forall l : List I, Exists (fun x : I => Not (List.Mem x l)))
    (a : I -> E) : E :=
  @dite E (Exists (fun e : E => Exists (fun l : List I => forall x : I, Not (List.Mem x l) -> a x = e)))
    (Classical.propDecidable _) (fun _e => Classical.choose _e)
    (fun _ => Classical.choice (Nonempty.intro (a (Classical.choose (h [])))))

private theorem _default_spec {I E : Type} (h : forall l : List I, Exists (fun x : I => Not (List.Mem x l)))
    (a : I -> E) (e : E) (l : List I) (_he : forall x : I, Not (List.Mem x l) -> a x = e) : _default h a = e := by
  have _ex : Exists (fun e : E => Exists (fun l : List I => forall x : I, Not (List.Mem x l) -> a x = e)) :=
    Exists.intro e (Exists.intro l _he)
  unfold _default
  rw [dite_eq_left _ex]
  obtain ⟨l2, h2⟩ := Classical.choose_spec _ex
  obtain ⟨x, hx⟩ := h (l ++ l2)
  have _x1 : Not (List.Mem x l) := fun m => hx (List.mem_append.mpr (Or.inl m))
  have _x2 : Not (List.Mem x l2) := fun m => hx (List.mem_append.mpr (Or.inr m))
  rw [← h2 x _x2, _he x _x1]

private theorem _default_const {I E : Type} (h : forall l : List I, Exists (fun x : I => Not (List.Mem x l)))
    (v : E) : _default h (_const_array I v) = v :=
  _default_spec h _ v [] (fun _ _ => rfl)

private theorem _default_store {I E : Type} (h : forall l : List I, Exists (fun x : I => Not (List.Mem x l)))
    (a : I -> E) (i : I) (v : E) : _default h (_store a i v) = _default h a := by
  by_cases _ex : Exists (fun e : E => Exists (fun l : List I => forall x : I, Not (List.Mem x l) -> a x = e))
  . obtain ⟨e, l, he⟩ := _ex
    rw [_default_spec h a e l he]
    refine _default_spec h _ e (i :: l) (fun x hx => ?_)
    have _xi : Not (x = i) := fun q => hx (q ▸ List.Mem.head l)
    have _xl : Not (List.Mem x l) := fun m => hx (List.Mem.tail i m)
    simp only [_store, _xi, ite_false]
    exact he x _xl
  . have _ns : Not (Exists (fun e : E => Exists (fun l : List I =>
        forall x : I, Not (List.Mem x l) -> _store a i v x = e))) := by
      intro ⟨e, l, he⟩
      apply _ex
      refine Exists.intro e (Exists.intro (i :: l) (fun x hx => ?_))
      have _xi : Not (x = i) := fun q => hx (q ▸ List.Mem.head l)
      have _xl : Not (List.Mem x l) := fun m => hx (List.Mem.tail i m)
      have := he x _xl
      simp only [_store, _xi, ite_false] at this
      exact this
    unfold _default
    rw [dite_eq_right _ex, dite_eq_right _ns]
""".strip("\n").split("\n")
# The default value of a map, (= (default (map f a b)) (f (default a)
# (default b))), the array solver's default-map axiom, is not a theorem of
# that _default: an argument of the map need not be constant at all but
# finitely many indices. When a refutation uses the axiom and the input
# names no default value (_generic_defaults), the default values are the
# array solver's own terms, and one function has all three properties over
# the terms of the certificate: the read at one index g that no store of the
# certificate writes. There a constant array has its value, a store the
# value of the array it writes into (g is not the stored index), and a map
# its function of the arrays' values, whatever the element sort. Such an
# index exists (no finite list exhausts the index type), so it is a
# definition over the interpretation (_generic_index_definitions:
# Classical.choose of the unboundedness theorem at the list of the stored
# indices), not a hypothesis of the theorem, whose assertions do not
# mention it. _default keeps its name, with that index in the place of the
# unboundedness proof; _default_store takes the proof that the index is not
# the stored one, which _fresh_ne gives for a member of the list.
_GENERIC_DEFAULT_DEFINITIONS = """
def _default {I E : Type} (g : I) (a : I -> E) : E := a g

private theorem _default_const {I E : Type} (g : I) (v : E) : _default g (_const_array I v) = v := rfl

private theorem _default_store {I E : Type} (g : I) (a : I -> E) (i : I) (v : E) (h : Not (g = i)) :
    _default g (_store a i v) = _default g a := _store_off a i v g h

private theorem _fresh_ne {I : Type} (l : List I) (g : I) (h : Not (List.Mem g l)) (x : I) (m : List.Mem x l) :
    Not (g = x) := fun _e => h (_e ▸ m)
""".strip("\n").split("\n")
# Maps ((_ map f) a b) and Z3's set operators (maps of connectives over sets,
# I -> Prop) are the pointwise function, _map1, _map2, or _map3 of a Lean
# function. A read of one is that function over the reads, by rfl (the array
# solver's select-map axiom, stated per read by _array_helpers). Its default
# value is not determined by the arguments' (an argument need not be constant
# at all but finitely many indices), so the default-map axiom is certified
# only with the default values read at a generic index
# (_GENERIC_DEFAULT_DEFINITIONS), and rejected when the input names a default
# value (by the exporter's replay when a refutation uses it, and by
# _check_th_lemma).
# The connective of a map or set operator by name (map parameter) or by
# kind: the Lean function, then the number of arrays.
_MAP_CONNECTIVES = {"not": ("Not", 1), "and": ("And", 2), "or": ("Or", 2),
                    "=>": ("(fun _p _q : Prop => _p -> _q)", 2)}
# The other functions a map may apply (proof_certificate.MAP_FUNCTIONS), by
# name: the element sorts they admit, their arities, and their body over
# the rendered arguments and Lean argument types, as the formula and term
# renderers write the application (_formula_body, _term_body), so that the
# beta-reduced read facts match the lemmas' terms. "same" admits two
# arguments of one sort; "numeric" Int or Real; "bool" Bool alone; the
# result follows. Uninterpreted functions ("declared") are rendered as
# their family applied to the injected arguments (_map_application).
# The negation of an Int map is the difference from zero, as every Int
# negation is: the store and constant-array identities apply the function
# to a stored value, and at the value 0 grind would beta-reduce a negation
# to -0, which it mistakes for another numeral than 0 (see _negation).
_INT_MAP_NEGATION = "(((0 : Int)) - %s)"
_MAP_BUILTINS = {
    "xor": ("bool", (2,), lambda args, types: "(Or (And %s (Not %s)) (And (Not %s) %s))" % (
        args[0], args[1], args[0], args[1])),
    "=": ("same", (2,), lambda args, types: ("(Iff %s %s)" if types[0] == "Prop" else "(%s = %s)") % tuple(args)),
    "distinct": ("same", (2,), lambda args, types: (
        "(Not (Iff %s %s))" if types[0] == "Prop" else "(Not (%s = %s))") % tuple(args)),
    "+": ("numeric", (2,), lambda args, types: "(%s + %s)" % tuple(args)),
    "-": ("numeric", (1, 2), lambda args, types: (
        (_INT_MAP_NEGATION if types[0] == "Int" else "(-%s)") % args[0] if len(args) == 1
        else "(%s - %s)" % tuple(args))),
    "<=": ("numeric", (2,), lambda args, types: "(%s <= %s)" % tuple(args)),
    "<": ("numeric", (2,), lambda args, types: "(%s < %s)" % tuple(args)),
    ">=": ("numeric", (2,), lambda args, types: "(%s >= %s)" % tuple(args)),
    ">": ("numeric", (2,), lambda args, types: "(%s > %s)" % tuple(args)),
    "ite": ("ite", (3,), lambda args, types: (
        "(Or (And %s %s) (And (Not %s) %s))" % (args[0], args[1], args[0], args[2]) if types[1] == "Prop"
        else "(@ite %s %s (Classical.propDecidable _) %s %s)" % (types[1], args[0], args[1], args[2]))),
}
# Maps whose function commutes, which Z3's congruence closure may use
# (array_decl_plugin inherits commutativity from the function).
_COMMUTATIVE_MAPS = ("xor", "=", "distinct", "+")
_DECLARED_MAP = "declared"
_SET_OPERATOR_NAMES = dict(SET_OPERATORS)
_SET_OPERATOR_FUNCTIONS = {z3.Z3_OP_SET_UNION: "Or", z3.Z3_OP_SET_INTERSECT: "And",
                           z3.Z3_OP_SET_DIFFERENCE: "(fun _p _q : Prop => And _p (Not _q))",
                           z3.Z3_OP_SET_COMPLEMENT: "Not"}
# The congruence closure of Z3's euf solver treats maps of and and or as
# commutative, and its rewriter simplifies maps (_map_identities): the
# commutativity and idempotence theorems of each, by Lean function.
_SET_IDENTITIES = {"And": ("_map2_and_comm", "_map2_and_self"), "Or": ("_map2_or_comm", "_map2_or_self")}
# Each function applied to the reads, beta-reduced (the facts grind is given).
_SET_FUNCTION_BODIES = {"Not": "(Not %s)", "And": "(And %s %s)", "Or": "(Or %s %s)",
                        "(fun _p _q : Prop => _p -> _q)": "(%s -> %s)",
                        "(fun _p _q : Prop => And _p (Not _q))": "(And %s (Not %s))"}
_SET_DEFINITIONS = """
def _map1 {I E G : Type} (f : E -> G) (a : I -> E) : I -> G := fun _i => f (a _i)

def _map2 {I E F G : Type} (f : E -> F -> G) (a : I -> E) (b : I -> F) : I -> G := fun _i => f (a _i) (b _i)

def _map3 {I E F H G : Type} (f : E -> F -> H -> G) (a : I -> E) (b : I -> F) (c : I -> H) : I -> G :=
  fun _i => f (a _i) (b _i) (c _i)

private theorem _map2_and_comm {I : Type} (a b : I -> Prop) : _map2 And a b = _map2 And b a :=
  funext (fun _i => propext And.comm)

private theorem _map2_or_comm {I : Type} (a b : I -> Prop) : _map2 Or a b = _map2 Or b a :=
  funext (fun _i => propext Or.comm)

private theorem _map2_comm {I E G : Type} (f : E -> E -> G) (h : forall x y, f x y = f y x) (a b : I -> E) :
    _map2 f a b = _map2 f b a := funext (fun _i => h (a _i) (b _i))

private theorem _map1_not_not {I : Type} (a : I -> Prop) : _map1 Not (_map1 Not a) = a :=
  funext (fun _i => propext Classical.not_not)

private theorem _map2_and_self {I : Type} (a : I -> Prop) : _map2 And a a = a := funext (fun _i => and_self _)

private theorem _map2_or_self {I : Type} (a : I -> Prop) : _map2 Or a a = a := funext (fun _i => or_self _)

private theorem _map1_store {I E G : Type} (f : E -> G) (a : I -> E) (i : I) (v : E) :
    _map1 f (_store a i v) = _store (_map1 f a) i (f v) := by
  funext _j
  by_cases _h : _j = i <;> simp [_map1, _store, _h]

private theorem _map2_store {I E F G : Type} (f : E -> F -> G) (a : I -> E) (b : I -> F) (i : I) (v : E) (w : F) :
    _map2 f (_store a i v) (_store b i w) = _store (_map2 f a b) i (f v w) := by
  funext _j
  by_cases _h : _j = i <;> simp [_map2, _store, _h]

private theorem _map3_store {I E F H G : Type} (f : E -> F -> H -> G) (a : I -> E) (b : I -> F) (c : I -> H)
    (i : I) (u : E) (v : F) (w : H) :
    _map3 f (_store a i u) (_store b i v) (_store c i w) = _store (_map3 f a b c) i (f u v w) := by
  funext _j
  by_cases _h : _j = i <;> simp [_map3, _store, _h]
""".strip("\n").split("\n")
_ARRAY_COMPONENT_NAME = re.compile(r"[^\s()|]+")
# The deepest nesting of array sort names _array_components parses (each
# level one recursion of it and of the functions over its components).
_ARRAY_NESTING = 64
# Z3's array rewriter simplifies (store (store a i v) i w) to (store a i w)
# and (store a i (select a i)) to a, which the clause-log replay then ties to
# the assertion by a rewrite; a lemma reaching a store may need these
# identities, which grind does not derive (they need funext). Next to
# constant arrays it also evaluates (select (const c) j) to c and folds
# (store (const c) i c) into (const c), so the simp set gets _select_const
# and _const_store_self reversed as well (_grind_lemma). simp may use
# either identity or neither, so its unused-argument lint (an error under
# warningAsError) is off for this one tactic; that is a lint, not a check.
_ARRAY_REWRITE_TACTIC = "try (set_option linter.unusedSimpArgs false in simp only [%s_store_store, _store_select] at *)"


def _store_identity_instance(graph, nodes):
    """Whether nodes hold the left side of _store_store, _store_select, _const_store_self, or _const_eq_store.

    That is (store (store a i v) i w) or (store a i (select a i)), with the
    same index and array nodes (the certificate's terms are shared), a
    store into a constant array of its own value, (store (const c) i c),
    the value possibly a read of a constant array of c (Z3's rewriter
    evaluates the read to c first), or an equality between a constant array
    and a store into it, (= (const c) (store (const c) i v)), either way
    round. Indices and values match also as numeral expressions of one
    value ((/ 2 2) and 1.0, (+ 1 1) and 2), which the rewriter evaluates
    before applying the identity; the simp alternative then gets their
    values first (_numeral_facts).
    """
    for node in nodes:
        if graph.kind(node) == z3.Z3_OP_EQ and graph.is_array(graph.arguments(node)[0]):
            for constant, store in (graph.arguments(node), reversed(graph.arguments(node))):
                if (graph.kind(constant) == z3.Z3_OP_CONST_ARRAY and graph.kind(store) == z3.Z3_OP_STORE
                        and graph.arguments(store)[0] == constant):
                    return True
        if graph.kind(node) != z3.Z3_OP_STORE:
            continue
        array, index, value = graph.arguments(node)
        if graph.kind(array) == z3.Z3_OP_STORE and _same_value(graph, graph.arguments(array)[1], index):
            return True
        if (graph.kind(value) == z3.Z3_OP_SELECT and graph.arguments(value)[0] == array
                and _same_value(graph, graph.arguments(value)[1], index)):
            return True
        if (graph.kind(array) == z3.Z3_OP_CONST_ARRAY
                and _same_value(graph, _constant_value(graph, value), graph.arguments(array)[0])):
            return True
    return False


def _same_value(graph, left, right):
    """Whether two nodes are one node or numeral expressions of one value (_numeral_expression_value)."""
    if left == right:
        return True
    value = _numeral_expression_value(graph, left)
    return value is not None and value == _numeral_expression_value(graph, right)


# The operators of a numeral expression whose value Lean's grind computes.
_NUMERAL_OPERATORS = {z3.Z3_OP_ADD: sum, z3.Z3_OP_SUB: lambda values: values[0] - sum(values[1:]),
                      z3.Z3_OP_UMINUS: lambda values: -values[0],
                      z3.Z3_OP_MUL: lambda values: math.prod(values, start=Fraction(1))}


def _numeral_expression_value(graph, node):
    """The value of an arithmetic node built from numerals by + - * / and to_real, or None.

    Division by an expression of value 0 is not evaluated: Z3 leaves it
    uninterpreted, while Lean's x / 0 is 0. Unlike _numeral_value, this
    reads no linear form, so the divisor is a numeral expression too.
    Values are cached in graph.numeral_values, and evaluation stops at the
    first argument that is not a numeral expression.
    """
    if node not in graph.numeral_values:
        graph.numeral_values[node] = _evaluate_numeral_expression(graph, node)
    return graph.numeral_values[node]


def _evaluate_numeral_expression(graph, node):
    """_numeral_expression_value of a node, given those of its arguments."""
    if not graph.is_arith(node):
        return None
    kind, arguments = graph.kind(node), graph.arguments(node)
    if kind == z3.Z3_OP_ANUM:
        return Fraction(graph.decl(node).name)
    if not arguments:
        return None
    values = []
    for argument in arguments:
        value = _numeral_expression_value(graph, argument)
        if value is None:
            return None
        values.append(value)
    if kind == z3.Z3_OP_DIV:
        return None if len(values) != 2 or values[1] == 0 else values[0] / values[1]
    if kind == z3.Z3_OP_TO_REAL:
        return values[0]
    operation = _NUMERAL_OPERATORS.get(kind)
    return None if operation is None else operation(values)


def _numeral_facts(graph, reachable, atom_indices, variable_indices):
    """The value of each numeral expression a step reaches that is not a numeral, as have lines and simp names.

    That is, each one that is an argument of a term that is not a numeral
    expression ((- (+ 2 1) 1), not the (+ 2 1) under it): the simp
    alternative of _grind_lemma rewrites them to their values before the
    store identities, whose sides then match syntactically as they did for
    Z3's rewriter, which compares the values. The names are marked for
    simp's pre-order (↓), so an outer expression is rewritten before an
    inner one that also occurs on its own would change it. Numerals in the
    certificate's own forms, (- 1) and (/ 1 2), render as _numeral renders
    their values and get no fact (_rendered_as_numeral). Each fact is
    proved by grind.
    """
    lines, names = [], []
    outermost = set()
    for parent in sorted(reachable):
        if _numeral_expression_value(graph, parent) is not None:
            continue
        for node in graph.arguments(parent):
            if (node not in outermost and not _rendered_as_numeral(graph, node)
                    and _numeral_expression_value(graph, node) is not None):
                outermost.add(node)
    for node in sorted(outermost):
        name = "_nv%d" % node
        lines.append("have %s : (%s) = %s := by grind" % (
            name, _inline(graph, node, atom_indices, variable_indices),
            _numeral(graph.decl(node).range, _numeral_expression_value(graph, node))))
        names.append("↓ " + name)
    return lines, names


def _rendered_as_numeral(graph, node):
    """Whether a node renders as _numeral renders its value: a numeral, (- n), (/ n d), or (/ (- n) d), reduced."""
    kind, arguments = graph.kind(node), graph.arguments(node)

    def natural(argument):
        return (graph.kind(argument) == z3.Z3_OP_ANUM and Fraction(graph.decl(argument).name).denominator == 1
                and Fraction(graph.decl(argument).name) > 0)

    if kind == z3.Z3_OP_ANUM:
        return True
    if kind == z3.Z3_OP_UMINUS:
        return natural(arguments[0])
    if kind != z3.Z3_OP_DIV or len(arguments) != 2:
        return False
    numerator = arguments[0]
    if graph.kind(numerator) == z3.Z3_OP_UMINUS:
        numerator = graph.arguments(numerator)[0]
    if not (natural(numerator) and natural(arguments[1])):
        return False
    denominator = Fraction(graph.decl(arguments[1]).name)
    return denominator > 1 and (Fraction(graph.decl(numerator).name) / denominator).denominator == denominator


def _constant_value(graph, node):
    """The node a term evaluates to through reads of constant arrays, (select (const c) j) to c."""
    while graph.kind(node) == z3.Z3_OP_SELECT and graph.kind(graph.arguments(node)[0]) == z3.Z3_OP_CONST_ARRAY:
        node = graph.arguments(graph.arguments(node)[0])[0]
    return node


def _set_function(graph, node):
    """The Lean function of a map or set operator node, or None for any other node.

    A connective is named (Not, And, ...); any other function is a lambda
    over the elements, its body that of _map_application.
    """
    kind = graph.kind(node)
    if kind != z3.Z3_OP_ARRAY_MAP:
        return _SET_OPERATOR_FUNCTIONS.get(kind)
    name = graph.decl(node).parameters[0]
    if name in _MAP_CONNECTIVES:
        return _MAP_CONNECTIVES[name][0]
    types = [_array_types(graph, sort)[1] for sort in graph.decl(node).domain]
    variables = ["_v%d" % index for index in range(len(types))]
    return "(fun %s => %s)" % (" ".join("(%s : %s)" % pair for pair in zip(variables, types)),
                               _map_application(graph, node, variables))


def _map_application(graph, node, args):
    """The function of a map or set operator node applied to rendered elements, beta-reduced.

    An uninterpreted function is its family and index (_Graph.map_heads)
    applied to the elements injected into the carrier, as _term_body and
    _formula_body render an application of it.
    """
    kind, decl = graph.kind(node), graph.decl(node)
    if kind != z3.Z3_OP_ARRAY_MAP:
        return _SET_FUNCTION_BODIES[_SET_OPERATOR_FUNCTIONS[kind]] % tuple(args)
    name = decl.parameters[0]
    if name in _MAP_CONNECTIVES:
        return _SET_FUNCTION_BODIES[_MAP_CONNECTIVES[name][0]] % tuple(args)
    elements = [_array_components(sort)[1] for sort in decl.domain]
    if name == _DECLARED_MAP:
        head = graph.map_heads.get(graph.nodes[node].declaration)
        if head is None:
            raise ReconstructionError("map of an unbound function: %s" % decl.parameters[1])
        return "(%s [%s])" % (head, ", ".join(
            "(%s %s)" % (_INJECTIONS[sort], arg) if sort in _ARITH_SORTS else "(_m.bool %s)" % arg if sort == "Bool"
            else "(%s %s)" % (_sort_family(graph, sort, "inj"), arg) if sort in graph.index_sorts
            else arg for sort, arg in zip(elements, args)))
    return _MAP_BUILTINS[name][2](args, [_component_type(graph, sort) for sort in elements])


def _map_signature(parameters, elements, result):
    """Whether the function a map's parameters name takes elements of these sorts to one of result's.

    Element sorts are uninterpreted, Int, Real, or Bool, not arrays. A
    declared function's own signature is bound to the input's (_bind_input).
    """
    if any(_array_components(sort) for sort in list(elements) + [result]):
        return False
    name = parameters[0]
    if name in _MAP_CONNECTIVES:
        return list(elements) == ["Bool"] * _MAP_CONNECTIVES[name][1] and result == "Bool"
    if name == _DECLARED_MAP:
        return 1 <= len(elements) <= MAP_ARITY
    shape, arities, _ = _MAP_BUILTINS[name]
    if len(elements) not in arities:
        return False
    if shape == "bool":
        return all(sort == "Bool" for sort in elements) and result == "Bool"
    if shape == "same":
        return elements[0] == elements[1] and result == "Bool"
    if shape == "numeric":
        comparison = name not in ("+", "-")
        return (elements[0] in _ARITH_SORTS and all(sort == elements[0] for sort in elements)
                and result == ("Bool" if comparison else elements[0]))
    return elements[0] == "Bool" and elements[1] == elements[2] == result  # ite


def _map_symbol(graph, declaration):
    """The (name, element domain, element range) of the uninterpreted function a map declaration applies, or None."""
    decl = graph.declarations[declaration]
    if decl.kind != z3.Z3_OP_ARRAY_MAP or decl.parameters[0] != _DECLARED_MAP:
        return None
    return (decl.parameters[1], tuple(_array_components(sort)[1] for sort in decl.domain),
            _array_components(decl.range)[1])


def _symbol_signature(graph, declaration):
    """The (domain, range) of a symbol table entry: a declaration, or a map of an uninterpreted function."""
    symbol = _map_symbol(graph, declaration)
    if symbol is not None:
        return symbol[1:]
    decl = graph.declarations[declaration]
    return decl.domain, decl.range


@functools.lru_cache(maxsize=None)
def _array_components(name):
    """The index and element sort names of a certificate array sort name, None for any other sort name.

    Either component is a sort name without spaces or parentheses or,
    for nested arrays, an array sort name itself: (Array Int (Array Int
    Int)) has the components Int and (Array Int Int).
    """
    if not (name.startswith("(Array ") and name.endswith(")")):
        return None
    body, components, depth, start = name[len("(Array "):-1], [], 0, 0
    for position, character in enumerate(body + " "):
        if character == "(":
            depth += 1
            if depth > _ARRAY_NESTING:
                return None  # A rejection, not a RecursionError, for a tampered name.
        elif character == ")":
            depth -= 1
            if depth < 0:
                return None
        elif character == " " and depth == 0:
            components.append(body[start:position])
            start = position + 1
    if depth != 0 or len(components) != 2:
        return None
    for component in components:
        if not (_ARRAY_COMPONENT_NAME.fullmatch(component) or _array_components(component)):
            return None
    return tuple(components)


def _component_type(graph, sort):
    """The Lean type of a sort: Int, Rat, Prop (Bool), a function (an array), its own type (_index_sorts), or _m.U."""
    if _array_components(sort):
        return "(%s -> %s)" % _array_types(graph, sort)
    if sort in graph.index_sorts:
        return "_m.S%d" % graph.index_sorts.index(sort)
    return "Prop" if sort == "Bool" else _NUMBER_TYPES.get(sort, "_m.U")


def _array_sort_names(name):
    """The sort name itself and, for an array sort, the names of its components, through nested arrays."""
    components = _array_components(name) or ()
    return (name,) + tuple(inner for component in components for inner in _array_sort_names(component))


def _array_types(graph, name):
    """The Lean index and element types of a certificate array sort name."""
    return tuple(_component_type(graph, component) for component in _array_components(name))


# The Lean proof that no finite list exhausts an index sort over which
# constant arrays and default values are admitted (_CONSTANT_ARRAY_DEFINITIONS).
_UNBOUNDED = {"Int": "_int_unbounded", "Real": "_rat_unbounded"}


def _unbounded(graph, node, explicit=False):
    """The unboundedness proof of an array node's index type for _default, with the type itself if explicit.

    explicit gives `(I := Int) _int_unbounded`, for _default_const, whose
    array argument does not name the index type. With the default values
    read at a generic index (_Graph.generic), that index stands in the
    proof's place.
    """
    index = _array_components(graph.decl(node).range)[0]
    proof = "(%s _atoms%s)" % (_generic_index(index), graph.valuation) if graph.generic else _UNBOUNDED[index]
    if explicit:
        return "(I := %s) %s" % (_component_type(graph, index), proof)
    return proof


def _index_witness(graph, sort):
    """An index of an index sort without a default value (_UNBOUNDED), at which compared arrays are read.

    Over such a sort (uninterpreted or Bool) two constant arrays are equal
    exactly when their values are, since the sort has an index:
    _constant_array_comparisons reads them there. A formula is one over
    Bool; an uninterpreted sort has the values of its constants, named by
    the input or not (the families elems of the carrier and of a type of
    its own, _sort_family).
    """
    return "True" if sort == "Bool" else "(%s 0)" % _sort_family(graph, sort, "elems")


def _generic_index(sort):
    """The name of the generic index of an index sort of _UNBOUNDED: _generic_i (Int), _generic_r (Real)."""
    return "_generic_" + _ARRAY_TYPE_CODES[_NUMBER_TYPES[sort]]


def _default_map_axiom(graph, node):
    """Whether an array th-lemma states the default value of a map (the array solver's default-map axiom).

    The axiom is (= (default (map f a b)) (f (default a) (default b))).
    Any literal equating the default value of a map or set operator with
    another term counts, except the default value of a store over that map,
    (= (default (store m i v)) (default m)), which is _default_store's.
    """
    for literal in graph.clause(graph.conclusion(node)):
        atom = graph.arguments(literal)[0] if graph.kind(literal) == z3.Z3_OP_NOT else literal
        if graph.kind(atom) != z3.Z3_OP_EQ:
            continue
        sides = graph.arguments(atom)
        for side, other in (sides, sides[::-1]):
            if (graph.kind(side) == z3.Z3_OP_ARRAY_DEFAULT
                    and (graph.kind(graph.arguments(side)[0]) == z3.Z3_OP_ARRAY_MAP
                         or graph.kind(graph.arguments(side)[0]) in _SET_OPERATOR_NAMES)
                    and not (graph.kind(other) == z3.Z3_OP_ARRAY_DEFAULT
                             and graph.kind(graph.arguments(other)[0]) == z3.Z3_OP_STORE
                             and graph.arguments(graph.arguments(other)[0])[0] == graph.arguments(side)[0])):
                return True
    return False


def _generic_defaults(graph):
    """Decide whether the default values are read at a generic index; return the nodes that mention a default value.

    They are when an array th-lemma states the default value of a map
    (_default_map_axiom), no assertion mentions a default value (the
    theorem's hypotheses then do not mention the index, and every default
    value is a term of the array solver), and no index stored at mentions
    one (the index is chosen off the stored indices, which must be defined
    before it). _Graph.generic then maps each index sort of _UNBOUNDED that
    indexes an array of the certificate to the index nodes of the stores
    over it, in order (_generic_index_definitions); it stays empty
    otherwise, and _check_th_lemma rejects the axiom.

    Every such index sort has an index, not only those a default term of
    the certificate is taken over: a rewrite or cnf lemma that compares
    arrays states the default value of each store and constant array it
    reaches (_constant_array_comparisons), whether or not the solver took
    one.
    """
    mentions = set()
    for node in range(len(graph.nodes)):
        if graph.kind(node) == z3.Z3_OP_ARRAY_DEFAULT or any(
                argument in mentions for argument in graph.arguments(node)):
            mentions.add(node)
    if not mentions or not any(
            graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA and graph.decl(node).parameters[:1] == ("array",)
            and _default_map_axiom(graph, node) for node in range(len(graph.nodes))):
        return mentions
    if any(assertion in mentions for assertion in graph.assertions):
        return mentions
    indices = {sort: set() for sort in _UNBOUNDED if any(_array_components(array)[0] == sort for array in graph.arrays)}
    for node in range(len(graph.nodes)):
        if graph.kind(node) == z3.Z3_OP_STORE and _array_components(graph.decl(node).range)[0] in indices:
            if graph.arguments(node)[1] in mentions:
                return mentions
            indices[_array_components(graph.decl(node).range)[0]].add(graph.arguments(node)[1])
    graph.generic.update((sort, tuple(sorted(nodes))) for sort, nodes in indices.items())
    return mentions


def _generic_index_definitions(graph, signature):
    """Define the generic index of each index sort and prove it is none of the indices stored at (_Graph.generic).

    _generic_i is an Int outside the list of the stored Int indices
    (Classical.choose of _int_unbounded there), _generic_i_fresh its
    specification, and _generic_i_ne_K the fact that it is not the index
    node K, which _default_store takes (_default_store_fact). The index
    terms are definitions written before these (they mention no default
    value), the default values after.
    """
    lines = []
    for sort, nodes in graph.generic.items():
        name, lean_type = _generic_index(sort), _component_type(graph, sort)
        applied = "(%s _atoms%s)" % (name, graph.valuation)
        stored = "([%s] : List %s)" % (", ".join(_term(graph, node) for node in nodes), lean_type)
        lines.extend([
            "noncomputable def %s %s : %s :=" % (name, signature, lean_type),
            "  Classical.choose (%s %s)" % (_UNBOUNDED[sort], stored),
            "private theorem %s_fresh %s : Not (List.Mem %s %s) :=" % (name, signature, applied, stored),
            "  Classical.choose_spec (%s %s)" % (_UNBOUNDED[sort], stored),
        ])
        for position, node in enumerate(nodes):
            lines.extend([
                "private theorem %s_ne_%d %s : Not (%s = %s) :=" % (name, node, signature, applied, _term(graph, node)),
                "  _fresh_ne _ _ (%s_fresh _atoms%s) _ (%sList.Mem.head _%s)" % (
                    name, graph.valuation, "List.Mem.tail _ (" * position, ")" * position),
            ])
    return lines


def _default_store_fact(graph, store, arguments):
    """_default_store applied to the rendered arguments of a store node: (default (store a i v)) = (default a).

    At a generic index (_Graph.generic) it takes the proof that the index
    is not the stored one too.
    """
    fresh = ""
    if graph.generic:
        index = _array_components(graph.decl(store).range)[0]
        fresh = " (%s_ne_%d _atoms%s)" % (_generic_index(index), graph.arguments(store)[1], graph.valuation)
    return "_default_store %s %s%s" % (_unbounded(graph, store), arguments, fresh)


def _default_map_fact(graph, name, array, inline):
    """The default-map axiom of a map or set operator node at the generic index (_Graph.generic), as a fact.

    Its default value is the function over the default values of its
    arrays, by rfl like a read of the map (_map_read_facts).
    """
    default = "_default %s" % _unbounded(graph, array)
    return "  have %s : %s %s = %s := rfl" % (name, default, inline(array), _map_application(
        graph, array, ["(%s %s)" % (default, inline(argument)) for argument in graph.arguments(array)]))


def _constant_array_definitions(graph):
    """The constant-array prelude with the unboundedness theorems of the graph's array index sorts only."""
    indices = {_array_components(sort)[0] for sort in graph.arrays}
    lines = list(_CONSTANT_ARRAY_DEFINITIONS)
    for index in _UNBOUNDED:  # Int before Real, a fixed order
        if index in indices:
            lines.extend([""] + _UNBOUNDED_THEOREMS[index])
    return lines + [""] + (_GENERIC_DEFAULT_DEFINITIONS if graph.generic else _DEFAULT_DEFINITIONS)


def _array_family(graph, name):
    """The interpretation's family of the array constants of an array sort, one per Lean array type.

    Arrays between uninterpreted sorts keep the family arrs; the others are
    named by their index and element types (arrs_ii for (Array Int Int)),
    a nested array component by a, then its own two codes, a prefix code
    (arrs_iaii for (Array Int (Array Int Int)), arrs_aiii for (Array (Array
    Int Int) Int)).
    """
    codes = "".join(_array_type_code(graph, component) for component in _array_components(name))
    return "arrs" if codes == "uu" else "arrs_" + codes


def _array_type_code(graph, sort):
    """The family-name code of an array index or element sort (_array_family)."""
    components = _array_components(sort)
    if components:
        return "a" + "".join(_array_type_code(graph, component) for component in components)
    if sort in graph.index_sorts:
        return "s%d" % graph.index_sorts.index(sort)  # No other code has a digit, so the codes stay a prefix code.
    return _ARRAY_TYPE_CODES[_component_type(graph, sort)]


def _array_injection(graph, name):
    """The interpretation's map injecting an array argument of a function or predicate into the carrier.

    Like _m.real and _m.int, nothing states that it is injective and nothing
    needs it: lemmas only use congruence, a = b -> inj a = inj b. No map
    from U -> U or U -> Int into U is injective (Cantor), but a model is
    still an instance: only finitely many array values are denoted by the
    input's terms, so U is the model's carriers plus one fresh point per
    such value, the injection sends each denoted array to its point, and
    the functions and predicates read their array arguments back from them.
    """
    return _array_family(graph, name) + "_inj"


def _array_functions(graph, name):
    """The interpretation's family of the functions into an array sort, one per Lean array type.

    Like _m.funs and the numeric families, a function takes the list of its
    arguments in the carrier (each injected by its sort) and returns an
    array of the Lean type, so a model's function into arrays is an instance
    through the same embedding of its array values as the array constants.
    """
    return _array_family(graph, name) + "_funs"


def _array_family_fields(graph):
    """The interpretation's fields of the array families the certificate uses, their injections and functions."""
    fields = {}
    arguments = {sort for decl in graph.declarations if decl.kind == z3.Z3_OP_UNINTERPRETED
                 for sort in decl.domain if sort in graph.arrays}
    results = {decl.range for decl in graph.declarations if decl.kind == z3.Z3_OP_UNINTERPRETED and decl.domain}
    for sort in graph.arrays:
        index, element = (lean.replace("_m.", "") for lean in _array_types(graph, sort))
        fields.setdefault(_array_family(graph, sort), "Nat -> %s -> %s" % (index, element))
        if sort in arguments:
            fields.setdefault(_array_injection(graph, sort), "(%s -> %s) -> U" % (index, element))
        if sort in results:
            fields.setdefault(_array_functions(graph, sort), "Nat -> List U -> %s -> %s" % (index, element))
    return tuple(sorted(fields.items()))


def _nonempty(graph, sort):
    """The inhabitant of an array index sort the extensionality witness chooses with.

    An index sort that is an array is inhabited by a constant function,
    mapped from an inhabitant of its element sort.
    """
    components = _array_components(sort)
    if components:
        return "(Nonempty.elim %s (fun _e => Nonempty.intro (fun (_ : %s) => _e)))" % (
            _nonempty(graph, components[1]), _component_type(graph, components[0]))
    lean = _component_type(graph, sort)
    if lean == "Prop":
        return "(Nonempty.intro True)"
    if sort in graph.index_sorts:
        return "_m.%s_nonempty" % _array_type_code(graph, sort)
    return "_m.nonempty" if lean == "_m.U" else "(Nonempty.intro (0 : %s))" % lean


def _inhabitant_sort(sort):
    """The sort whose inhabitant _nonempty starts from: sort itself, or an array's innermost element sort."""
    while _array_components(sort):
        sort = _array_components(sort)[1]
    return sort
_UFLRA_BINDERS = " (_vars : Nat -> Rat)" + _UF_BINDERS
_UFLRA_ARGUMENTS = " _vars" + _UF_ARGUMENTS
_UFLIA_BINDERS = " (_vars : Nat -> Int)" + _UF_BINDERS
_UFLIA_ARGUMENTS = " _vars" + _UF_ARGUMENTS
_UFLIRA_BINDERS = " (_vars : Nat -> Rat) (_ivars : Nat -> Int)" + _UF_BINDERS
_UFLIRA_ARGUMENTS = " _vars _ivars" + _UF_ARGUMENTS
# The injection of a numeric argument into the carrier and the family of
# functions with a numeric result, by arithmetic sort.
_INJECTIONS = {"Real": "_m.real", "Int": "_m.int"}
_NUMERIC_FUNCTIONS = {"Real": "_m.rfuns", "Int": "_m.ifuns"}
_FIXED_PROOF_RULES = {
    z3.Z3_OP_PR_ASSERTED: ("asserted", 0),
    z3.Z3_OP_PR_HYPOTHESIS: ("hypothesis", 0),
    # The legacy core states its theory axioms as (or false l) and resolves
    # the false literal away with the unit true.
    z3.Z3_OP_PR_TRUE: ("true-axiom", 0),
    z3.Z3_OP_PR_LEMMA: ("lemma", 1),
    z3.Z3_OP_PR_MODUS_PONENS: ("mp", 2),
    z3.Z3_OP_PR_REWRITE: ("rewrite", 0),
    z3.Z3_OP_PR_DEF_AXIOM: ("def-axiom", 0),
    z3.Z3_OP_PR_REFLEXIVITY: ("refl", 0),
    z3.Z3_OP_PR_SYMMETRY: ("symm", 1),
    z3.Z3_OP_PR_TRANSITIVITY: ("trans", 2),
    z3.Z3_OP_PR_IFF_TRUE: ("iff-true", 1),
    z3.Z3_OP_PR_IFF_FALSE: ("iff-false", 1),
    z3.Z3_OP_PR_AND_ELIM: ("and-elim", 1),
    z3.Z3_OP_PR_NOT_OR_ELIM: ("not-or-elim", 1),
    z3.Z3_OP_PR_COMMUTATIVITY: ("commutativity", 0),
}
# Congruence of the classical ite over the carrier, stated once per file when
# a monotonicity step rewrites an ite term (the legacy core's conflict
# resolution does; the clause log never derives equalities between terms).
_ITE_CONGRUENCE = (
    "",
    "private theorem ite_congr_classical {_U : Type} {_c _c' : Prop} {_a _b _a' _b' : _U}",
    "    (_hc : Iff _c _c') (_ha : _a = _a') (_hb : _b = _b')",
    "    : @ite _U _c (Classical.propDecidable _c) _a _b = @ite _U _c' (Classical.propDecidable _c') _a' _b' := by",
    "  cases propext _hc; cases _ha; cases _hb; rfl",
)
_VARIADIC_PROOF_RULES = {
    z3.Z3_OP_PR_UNIT_RESOLUTION: ("unit-resolution", 1),
    z3.Z3_OP_PR_MONOTONICITY: ("monotonicity", 0),
    z3.Z3_OP_PR_TRANSITIVITY_STAR: ("trans*", 0),
    # A clause-log th-lemma has no premises; the legacy core's lists the
    # literals and equalities its conflict or propagation rests on.
    z3.Z3_OP_PR_TH_LEMMA: ("th-lemma", 0),
}


def _fields(value, names, label):
    if type(value) is not dict or set(value) != set(names):
        raise ReconstructionError("%s has missing or unexpected fields" % label)


def _index(value, limit, label):
    if type(value) is not int or not 0 <= value < limit:
        raise ReconstructionError("invalid %s index: %r" % (label, value))
    return value


def _list(value, label):
    if type(value) is not list:
        raise ReconstructionError("%s must be a list" % label)
    return value


def _unique_fields(pairs):
    result = {}
    for name, value in pairs:
        if name in result:
            raise ReconstructionError("duplicate JSON field: %s" % name)
        result[name] = value
    return result


def load_certificate(stream):
    """Load JSON without silently accepting duplicate object fields."""
    return json.load(stream, object_pairs_hook=_unique_fields)


@dataclass(frozen=True)
class _Declaration:
    kind: int
    name: str
    domain: tuple
    range: str
    parameters: tuple = ()


@dataclass(frozen=True)
class _Node:
    declaration: int
    arguments: tuple


@dataclass(frozen=True)
class _Graph:
    declarations: tuple
    nodes: tuple
    assertions: tuple
    proof: int
    arithmetic: bool = False
    sorts: tuple = ()  # the uninterpreted sort names, sorted
    # Whether the proof uses an uninterpreted sort or an uninterpreted predicate
    # over Bool alone: either takes the qf_uf encoding (a Bool-only predicate's
    # arguments are injected into the otherwise unused carrier).
    uninterpreted: bool = False
    numeric: str = "Real"  # the arithmetic sort of the certificate: Real, Int, or _MIXED (qf_lira, qf_uflira)
    floors: bool = False  # whether the certificate has a to_int or an is_int
    # The arithmetic sort of each qf_lira theory step, by node (_lemma_numeric).
    lemma_sorts: dict = field(default_factory=dict, compare=False, repr=False)
    # The polynomial refutation of each Int theory step over products, by node (_polynomial_certificate).
    polynomial_certificates: dict = field(default_factory=dict, compare=False, repr=False)
    # The family and index of each uninterpreted function a map applies, by
    # the map's declaration (_map_application), once the symbols are numbered.
    map_heads: dict = field(default_factory=dict, compare=False, repr=False)
    # The input's enumeration sorts among the sorts, by name: their constructor
    # names in declaration order (read from the input by _bind_input, never
    # from the certificate).
    enumerations: dict = field(default_factory=dict, compare=False, repr=False)
    # The value of each node evaluated by _numeral_expression_value, None if
    # it is not a numeral expression (a cache: the nodes form a shared DAG).
    numeral_values: dict = field(default_factory=dict, compare=False, repr=False)
    # The value of each node evaluated by _abs_free_value, None if it has
    # none (a cache, as numeral_values).
    abs_free_values: dict = field(default_factory=dict, compare=False, repr=False)
    # The keys of _real_argument_key and _real_atom_key, by ("argument" or
    # "atom", node) (a cache: keying a nested ite chain revisits each level
    # from its condition and both branches), and the interned atom key of
    # each atom key structure, by ("structure", structure).
    real_keys: dict = field(default_factory=dict, compare=False, repr=False)
    # The terms each formula floors (_floored_terms), by node (a cache: every
    # lemma's _real_argument_pairs visits the reachable formulas again).
    floored_terms: dict = field(default_factory=dict, compare=False, repr=False)
    # The auxiliary theorems _pointwise_map_facts has stated, by their text:
    # their names. A step that compares two sets as an earlier one did uses
    # that step's theorem, so the lines each call returns must be written
    # out, in the order of the calls (reconstruct writes the steps' lemmas
    # in node order).
    pointwise_theorems: dict = field(default_factory=dict, compare=False, repr=False)
    # When the default values are read at a generic index (_generic_defaults):
    # each unbounded index sort of the certificate's arrays -> the index
    # nodes of the stores over it, in order. Empty otherwise.
    generic: dict = field(default_factory=dict, compare=False, repr=False)
    # The characters of the declarations each swept cnf lemma has written, by
    # node (_cnf_refutation): the sweeps of a file share _SWEEP_CHARS.
    swept: dict = field(default_factory=dict, compare=False, repr=False)

    def constructor_index(self, name, sort):
        """The index of a constructor in _m.ctors: the enumerations by sort name, each in declaration order."""
        index = 0
        for enumeration in sorted(self.enumerations):
            if enumeration == sort and name in self.enumerations[sort]:
                return index + self.enumerations[sort].index(name)
            index += len(self.enumerations[enumeration])
        raise ReconstructionError("not a constructor of the input's enumeration %s: %s" % (sort, name))

    @property
    def fragment(self):
        if self.arithmetic and self.uninterpreted:
            return _MIXED_FRAGMENTS[self.numeric]
        if self.arithmetic:
            return {"Int": "qf_lia", _MIXED: "qf_lira"}.get(self.numeric, "qf_lra")
        return "qf_uf" if self.uninterpreted else "propositional"

    @functools.cached_property
    def arrays(self):
        """The array sort names among the sorts, (Array I E)."""
        return tuple(sort for sort in self.sorts if _array_components(sort))

    @functools.cached_property
    def carriers(self):
        """The uninterpreted sorts proper, rendered as _m.U except those of index_sorts."""
        return tuple(sort for sort in self.sorts if not _array_components(sort))

    @functools.cached_property
    def index_sorts(self):
        """The uninterpreted sorts with a Lean type of their own, _m.S0, _m.S1, ... in this order (_index_sorts)."""
        return _index_sorts(self)

    @functools.cached_property
    def constant_indices(self):
        """The index sorts without a default value (_UNBOUNDED) that constant arrays of the certificate are over."""
        return frozenset(_array_components(decl.range)[0] for decl in self.declarations
                         if decl.kind == z3.Z3_OP_CONST_ARRAY) - set(_UNBOUNDED)

    @functools.cached_property
    def subset_rewrite(self):
        """Whether _subset_eq is stated: a subset next to a constant array (_SUBSET_REWRITE)."""
        kinds = {decl.kind for decl in self.declarations}
        return z3.Z3_OP_SET_SUBSET in kinds and z3.Z3_OP_CONST_ARRAY in kinds

    def is_array(self, node):
        """Whether node is a term of an array sort."""
        return bool(self.arrays) and self.decl(node).range in self.arrays

    def lean_type(self, node):
        """The Lean type of a term node: Rat or Int, a function type for an array, its sort's type otherwise."""
        if self.is_arith(node):
            return self.number_type_of(node)
        return _component_type(self, self.decl(node).range)

    @property
    def valuation(self):
        """Extra Lean arguments of every formula: the numeric valuations, the uninterpreted interpretation, or both."""
        return {"qf_lra": " _vars", "qf_lia": " _vars", "qf_lira": " _vars _ivars", "qf_uf": _UF_ARGUMENTS,
                "qf_uflra": _UFLRA_ARGUMENTS, "qf_uflia": _UFLIA_ARGUMENTS,
                "qf_uflira": _UFLIRA_ARGUMENTS}.get(self.fragment, "")

    def is_int(self, node):
        """Whether an arithmetic term (or a linear form's atom) is Int-valued."""
        return self.decl(node).range == "Int"

    def number_type_of(self, node):
        """The Lean type valuing an arithmetic term: Rat for Real, Int for Int."""
        return _NUMBER_TYPES[self.decl(node).range]

    def integer_form(self, terms):
        """Whether a linear form (atoms -> coefficients) is over Int; a constant form is over the certificate's sort.

        In qf_lira a Real atom may reach Int atoms through to_real, so a
        form is over Int when all its atoms are: (<= (to_real n) 0.5) then
        keys like (<= n 0), which it is equivalent to.
        """
        if self.numeric != _MIXED:
            return self.numeric == "Int"
        return bool(terms) and all(self.is_int(variable) for variable in terms)

    @property
    def number_type(self):
        """The Lean type valuing the arithmetic variables: Rat for Real, Int for Int."""
        return _NUMBER_TYPES[self.numeric]

    def injection(self, node):
        """The map injecting a numeric argument of a function or predicate into the carrier, by its sort."""
        return _INJECTIONS[self.decl(node).range]

    def numeric_functions(self, node):
        """The indexed family of functions with a numeric result containing an application, by its sort."""
        return _NUMERIC_FUNCTIONS[self.decl(node).range]

    def function_family(self, node):
        """The indexed family of an application's function: numeric, into an array sort, or into its sort's type."""
        if self.is_arith(node):
            return self.numeric_functions(node)
        if self.is_array(node):
            return "_m." + _array_functions(self, self.decl(node).range)
        return _sort_family(self, self.decl(node).range, "funs")

    def is_arith(self, node):
        return self.decl(node).range in _ARITH_SORTS

    def is_term(self, node):
        """A Real or uninterpreted-sort node, as opposed to a formula or proof."""
        return self.decl(node).range not in ("Bool", "Proof")

    def decl(self, node):
        return self.declarations[self.nodes[node].declaration]

    def kind(self, node):
        return self.decl(node).kind

    def arguments(self, node):
        return self.nodes[node].arguments

    @functools.cached_property
    def equalities(self):
        """The equality nodes between two terms, by their (ordered) argument pair."""
        return {self.arguments(node): node for node in range(len(self.nodes))
                if self.kind(node) == z3.Z3_OP_EQ and len(self.arguments(node)) == 2
                and self.is_term(self.arguments(node)[0])}

    @functools.cached_property
    def distinct_term_sets(self):
        """How many distinct nodes range over each multiset of terms (its sorted argument tuple)."""
        return Counter(tuple(sorted(self.arguments(node))) for node in range(len(self.nodes))
                       if self.kind(node) == z3.Z3_OP_DISTINCT and self.arguments(node)
                       and self.is_term(self.arguments(node)[0]))

    @functools.cached_property
    def integer_products(self):
        """Whether some Int node is a product of two or more nonconstant factors (_is_product)."""
        return any(self.decl(node).range == "Int" and _is_product(self, node) for node in range(len(self.nodes)))

    def conclusion(self, node):
        return self.arguments(node)[-1]

    def clause(self, node):
        if self.kind(node) == z3.Z3_OP_FALSE:
            return ()
        if self.kind(node) == z3.Z3_OP_OR:
            return self.arguments(node)
        return (node,)


def _parameters(kind, name, parameters):
    """Validate declaration parameters: th-lemma carries a hint and its coefficients, a pseudo-Boolean
    constraint its bound and coefficients (integers; their count is checked against the domain by _declaration),
    a map its function (a built-in's name, or "declared" and an uninterpreted function's)."""
    parameters = _list(parameters, "declaration parameters")
    if any(type(parameter) is not str for parameter in parameters):
        raise ReconstructionError("declaration parameters must be strings")
    if kind == z3.Z3_OP_ARRAY_MAP:
        if not ((len(parameters) == 1 and (parameters[0] in _MAP_CONNECTIVES or parameters[0] in _MAP_BUILTINS))
                or (len(parameters) == 2 and parameters[0] == _DECLARED_MAP and parameters[1])):
            raise ReconstructionError("a map takes one supported function: %s" % name)
        return tuple(parameters)
    if kind in _PSEUDO_BOOLEAN:
        if any(re.fullmatch(r"-?(0|[1-9][0-9]*)", parameter) is None for parameter in parameters):
            raise ReconstructionError("pseudo-Boolean parameters must be integers: %s" % name)
        return tuple(parameters)
    if kind != z3.Z3_OP_PR_TH_LEMMA:
        if parameters:
            raise ReconstructionError("invalid or parameterized native declaration")
        return ()
    if not parameters or parameters[0] not in _HINTS:
        raise ReconstructionError("unsupported native proof rule: th-lemma without a supported theory hint")
    if parameters[0] in _COEFFICIENT_HINTS:
        try:
            if any(Fraction(parameter) < 0 for parameter in parameters[1:]):
                raise ValueError
        except (ValueError, ZeroDivisionError):
            raise ReconstructionError("th-lemma coefficients must be nonnegative rationals")
    elif len(parameters) != 1:
        raise ReconstructionError("%s th-lemma takes no coefficients" % parameters[0])
    return tuple(parameters)


def _uninterpreted_sorts(raws):
    """Return the uninterpreted and array sort names used by the declarations, sorted.

    An array sort's index and element sorts are sorts of the certificate
    even if no declaration names them otherwise; any other sort name with a
    parenthesis is rejected, so an array name is never an uninterpreted one.
    """
    sorts = set()
    for raw in raws:
        if type(raw) is dict:
            sorts.update(sort for sort in [raw.get("range")] + _list(raw.get("domain", []), "declaration domain")
                         if type(sort) is str and sort not in _RESERVED_SORTS)
    pending = list(sorts)
    while pending:
        sort = pending.pop()
        components = _array_components(sort)
        if components is None and ("(" in sort or ")" in sort):
            raise ReconstructionError("unsupported sort: %s" % sort)
        if components is not None:
            # Index and element sorts are uninterpreted, Int, Real, Bool (a
            # read of a set is a formula, an index over Bool too), or arrays
            # themselves (nested arrays, sorts of the certificate in turn).
            if any(component in _RESERVED_SORTS and component not in _ARITH_SORTS + ("Bool",)
                   for component in components):
                raise ReconstructionError("unsupported array sort: %s" % sort)
            for component in components:
                if component not in _RESERVED_SORTS and component not in sorts:
                    sorts.add(component)
                    pending.append(component)
    if "" in sorts:
        raise ReconstructionError("invalid uninterpreted sort name")
    return tuple(sorted(sorts))


def _declaration(raw, sorts):
    _fields(raw, ("kind", "name", "domain", "range", "parameters"), "declaration")
    kind, name = raw["kind"], raw["name"]
    domain = tuple(_list(raw["domain"], "declaration domain"))
    known = _RESERVED_SORTS + sorts
    if (type(kind) is not int or type(name) is not str
            or raw["range"] not in known or any(argument not in known for argument in domain)):
        raise ReconstructionError("invalid native declaration")
    parameters = _parameters(kind, name, raw["parameters"])
    # Functions and predicates take arguments of any uninterpreted sort, Bool,
    # Real, Int, or array sort (all but the first injected into the carrier,
    # each numeric sort and each Lean array type by its own map); Proof is
    # never an argument.
    argument_sorts = sorts + ("Bool", "Real", "Int")
    array = _array_components(raw["range"]) if raw["range"] in sorts else None
    if kind == z3.Z3_OP_SELECT:
        # A read of an array, of its element sort: uninterpreted, Int, Real,
        # Bool, or an array (a row of nested arrays).
        if (name != "select" or len(domain) != 2 or domain[0] not in sorts
                or _array_components(domain[0]) != (domain[1], raw["range"])):
            raise ReconstructionError("invalid select declaration")
    elif kind == z3.Z3_OP_ARRAY_EXT:
        # The extensionality witness, an index.
        if (name != "array-ext" or len(domain) != 2 or domain[0] != domain[1] or domain[0] not in sorts
                or (_array_components(domain[0]) or ("",))[0] != raw["range"]):
            raise ReconstructionError("invalid array-ext declaration")
    elif kind == z3.Z3_OP_ARRAY_DEFAULT:
        # The default value of an array over Int or Real indices (constant arrays).
        if (name != "default" or len(domain) != 1 or domain[0] not in sorts
                or _array_components(domain[0]) not in [(index, raw["range"]) for index in _UNBOUNDED]):
            raise ReconstructionError("invalid default declaration")
    elif kind == z3.Z3_OP_CONST_ARRAY:
        # A constant array, the constant function: not over array indices,
        # where a model's is constant on the embedded indices only (see
        # _ARRAY_TYPE_CODES); an uninterpreted index sort gets a type of
        # its own for it (_index_sorts).
        if (name != "const" or array is None or _array_components(array[0]) is not None
                or domain != (array[1],)):
            raise ReconstructionError("invalid constant array declaration")
    elif kind == z3.Z3_OP_ARRAY_MAP or kind in _SET_OPERATOR_NAMES:
        # A pointwise function over arrays of one index sort (map_parameters),
        # a set operator over sets of one sort. Not over arrays indexed by
        # arrays: the embedding of a model's outer arrays (fixed off the
        # embedded indices) does not commute with a function there (see
        # _ARRAY_TYPE_CODES).
        components = [_array_components(sort) if sort in sorts else None for sort in domain]
        if kind == z3.Z3_OP_ARRAY_MAP:
            valid = (name == "map" and array is not None and domain and None not in components
                     and all(component[0] == array[0] for component in components)
                     and _map_signature(parameters, [component[1] for component in components], array[1]))
        else:
            expected = _SET_OPERATOR_NAMES[kind]
            valid = (array is not None and array[1] == "Bool"
                     and (name, domain) == (expected[0], (raw["range"],) * expected[1]))
        if not valid or _array_components(array[0]) is not None:
            raise ReconstructionError("invalid map or set operator declaration: %s" % name)
    elif array is not None:
        # Array constants, functions into arrays (the family of their Lean
        # array type, _array_functions), ite, and store.
        if kind == z3.Z3_OP_ITE:
            if name != "if" or domain != ("Bool", raw["range"], raw["range"]):
                raise ReconstructionError("invalid array ite declaration")
        elif kind == z3.Z3_OP_STORE:
            if name != "store" or domain != (raw["range"],) + array:
                raise ReconstructionError("invalid store declaration")
        elif kind != z3.Z3_OP_UNINTERPRETED or any(argument not in argument_sorts for argument in domain):
            raise ReconstructionError("unsupported array declaration: %s" % name)
    elif raw["range"] in sorts:
        # Constants, functions, and ite inhabit an uninterpreted sort: no
        # definitions. Reads of an array and the extensionality witness
        # (an index) may too (checked above).
        if kind == z3.Z3_OP_ITE:
            if name != "if" or domain != ("Bool", raw["range"], raw["range"]):
                raise ReconstructionError("invalid uninterpreted-sort ite declaration")
        elif kind == z3.Z3_OP_DT_CONSTRUCTOR:
            # A constructor of an enumeration; _bind_input checks that the
            # input declares it, nullary, for this sort.
            if domain or not name or parameters:
                raise ReconstructionError("invalid enumeration constructor declaration: %s" % name)
        elif kind != z3.Z3_OP_UNINTERPRETED or any(argument not in argument_sorts for argument in domain):
            raise ReconstructionError("unsupported uninterpreted-sort declaration: %s" % name)
    elif raw["range"] in _ARITH_SORTS:
        numeric = raw["range"]
        if kind == z3.Z3_OP_ITE:
            if name != "if" or domain != ("Bool", numeric, numeric):
                raise ReconstructionError("invalid arithmetic ite declaration")
            return _Declaration(kind, name, domain, raw["range"], parameters)
        if kind == z3.Z3_OP_ANUM:
            try:
                value = Fraction(name)
            except (ValueError, ZeroDivisionError):
                raise ReconstructionError("invalid numeral declaration: %s" % name)
            if numeric == "Int" and value.denominator != 1:
                raise ReconstructionError("invalid Int numeral declaration: %s" % name)
        elif kind == z3.Z3_OP_UNINTERPRETED:
            # A Real or Int variable, or a function with a Real or Int result
            # (QF_UFLRA, QF_UFLIA).
            if any(argument not in argument_sorts for argument in domain):
                raise ReconstructionError("unsupported arithmetic function declaration: %s" % name)
            return _Declaration(kind, name, domain, raw["range"], parameters)
        elif kind == z3.Z3_OP_TO_REAL:
            # The injection of Int into Real, qf_lira only (a certificate
            # over one sort cannot declare it, see _validate_graph).
            if name != "to_real" or domain != ("Int",) or numeric != "Real":
                raise ReconstructionError("invalid to_real declaration")
            return _Declaration(kind, name, domain, raw["range"], parameters)
        elif kind == z3.Z3_OP_TO_INT:
            # The floor of a Real term, Rat.floor, qf_lira only like to_real.
            if name != "to_int" or domain != ("Real",) or numeric != "Int":
                raise ReconstructionError("invalid to_int declaration")
            return _Declaration(kind, name, domain, raw["range"], parameters)
        elif kind in _INT_NAMES:
            if _INT_NAMES[kind] != name or (numeric != "Int" and kind not in _NUMERIC_KINDS):
                raise ReconstructionError("unsupported arithmetic declaration: %s" % name)
        elif _REAL_NAMES.get(kind) != name or (kind == z3.Z3_OP_DIV and numeric == "Int"):
            raise ReconstructionError("unsupported arithmetic declaration: %s" % name)
        if any(sort != numeric for sort in domain):
            raise ReconstructionError("arithmetic declarations take %s arguments" % numeric)
        expected = _INT_ARITY.get(kind) or _REAL_ARITY.get(kind, 2)  # Associative operators have a binary domain.
        if len(domain) != expected:
            raise ReconstructionError("invalid arithmetic declaration arity: %s" % name)
    elif raw["range"] == "Bool":
        if kind == z3.Z3_OP_DT_IS:
            # The recognizer ((_ is c) t) of an enumeration, named by its
            # constructor c; _bind_input checks c against the input.
            if (len(domain) != 1 or domain[0] not in sorts or _array_components(domain[0]) is not None
                    or not name or parameters):
                raise ReconstructionError("invalid enumeration recognizer declaration: %s" % name)
        elif kind == z3.Z3_OP_IS_INT:
            # (is_int t) is (= (to_real (to_int t)) t), qf_lira only.
            if name != "is_int" or domain != ("Real",):
                raise ReconstructionError("invalid is_int declaration")
        elif kind == z3.Z3_OP_SET_SUBSET:
            # (subset a b) over two sets of one sort, not indexed by arrays
            # (as the set operators, see above).
            components = _array_components(domain[0]) if len(domain) == 2 and domain[0] in sorts else None
            if (name != "subset" or components is None or domain[1] != domain[0] or components[1] != "Bool"
                    or _array_components(components[0]) is not None):
                raise ReconstructionError("invalid subset declaration")
        elif kind in _PSEUDO_BOOLEAN:
            expected_name, _, weighted = _PSEUDO_BOOLEAN[kind]
            if (name != expected_name or any(argument != "Bool" for argument in domain)
                    or len(parameters) != 1 + (len(domain) if weighted else 0)):
                raise ReconstructionError("invalid pseudo-Boolean declaration: %s" % name)
        elif kind in _ARITH_PREDICATE_NAMES:
            if _ARITH_PREDICATE_NAMES[kind] != name or domain not in (("Real", "Real"), ("Int", "Int")):
                raise ReconstructionError("invalid arithmetic predicate declaration: %s" % name)
        else:
            if kind != z3.Z3_OP_UNINTERPRETED and _BOOL_NAMES.get(kind) != name:
                raise ReconstructionError("unsupported Boolean declaration: %s" % name)
            if kind == z3.Z3_OP_UNINTERPRETED and domain:
                # A predicate ranges over the uninterpreted sorts, Bool, and
                # Real or Int, possibly over Bool alone.
                if any(argument not in argument_sorts for argument in domain):
                    raise ReconstructionError("unsupported predicate declaration: %s" % name)
            else:
                argument_sort = "Bool"
                if kind in (z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT) and domain and domain[0] != "Proof":
                    # Equality and distinct compare terms of one sort: Bool, Real, or
                    # one uninterpreted sort. Proof terms are never compared.
                    argument_sort = domain[0]
                if any(argument != argument_sort for argument in domain):
                    raise ReconstructionError("Boolean declarations cannot mix argument sorts")
            expected = _FIXED_ARITY.get(kind)
            if kind in (z3.Z3_OP_AND, z3.Z3_OP_OR):
                expected = 2  # Native associative declarations have a binary domain.
            elif kind == z3.Z3_OP_UNINTERPRETED and domain:
                expected = len(domain)
            if expected is not None and len(domain) != expected:
                raise ReconstructionError("invalid Boolean declaration arity: %s" % name)
    elif kind in _FIXED_PROOF_RULES:
        expected_name, premises = _FIXED_PROOF_RULES[kind]
        if name != expected_name or domain != ("Proof",) * premises + ("Bool",):
            raise ReconstructionError("invalid %s declaration" % expected_name)
    elif kind in _VARIADIC_PROOF_RULES:
        expected_name, minimum = _VARIADIC_PROOF_RULES[kind]
        if (name != expected_name or len(domain) < minimum + 1 or domain[-1] != "Bool"
                or any(sort != "Proof" for sort in domain[:-1])):
            raise ReconstructionError("invalid %s declaration" % expected_name)
    else:
        raise ReconstructionError("unsupported native proof rule: %s" % name)
    return _Declaration(kind, name, domain, raw["range"], parameters)


def _pointwise_indices(graph):
    """The index sorts of the arrays that the maps, set operators, and subsets of the certificate are over."""
    indices = set()
    for decl in graph.declarations:
        if decl.kind == z3.Z3_OP_ARRAY_MAP or decl.kind in _SET_OPERATOR_NAMES:
            indices.add(_array_components(decl.range)[0])
        elif decl.kind == z3.Z3_OP_SET_SUBSET:
            indices.add(_array_components(decl.domain[0])[0])
    return indices


def _index_sorts(graph):
    """The uninterpreted index sorts of pointwise functions and constant arrays that get a Lean type of their own.

    Every uninterpreted sort is otherwise the one type _m.U, and an equality
    of arrays over a sort I is then stated at every index of _m.U. A model
    is an instance all the same while its arrays are only read, stored
    into, and chosen between: each is extended outside I by one fixed
    value, which those operations keep (see _ARRAY_TYPE_CODES). A map, a
    set operator, or a subset does not keep it (the complement of the fixed
    value is another value), so with them an equality of the input may hold
    in a model and fail in Lean outside I. (= (store a i true) (complement
    (store a i false))) says that I has one element, and is satisfiable
    next to (not (= e1 e2)) over another sort; over one carrier its two
    Lean hypotheses are contradictory (the carrier holds e1 and e2, and at
    one of them the sets differ), so a refutation resting on them would
    prove nothing about the input. A constant array does not keep it
    either: a model's is constant on I, and the fixed value outside. With
    _const_array over all of _m.U, (= (store (const v) i w) (store (const
    w) i w)) with (not (= v w)), which says that I has one element (and has
    a model: v and w are of another sort), would be contradictory too.

    So the index sort I of the arrays such a function is over (a map's
    result, a subset's sets, a constant array), in the order of the names,
    is a type _m.SK of its own, K its position
    here: the arrays over I are functions on exactly a model's I, their
    equalities, maps, subsets, and constant arrays mean what the input's
    do, and I's terms
    are families of their own (_sort_family) injected into _m.U where a
    function or predicate takes them. Unless I is all of _m.U anyway: the
    only uninterpreted sort (enumerations included, whose constructors
    inhabit the carrier), with no function, predicate, or mapped function
    taking an argument of another sort (a Bool, Int, Real, or array argument
    is injected into the carrier, which must then hold its values). Then
    the model's I itself is the carrier, and the encoding stays as it is
    without maps. Int, Real, and Bool indices are Lean's own types; maps
    and constant arrays over arrays indexed by arrays are rejected
    (_declaration).
    """
    indices = _pointwise_indices(graph) | {_array_components(decl.range)[0] for decl in graph.declarations
                                           if decl.kind == z3.Z3_OP_CONST_ARRAY}
    indices = tuple(sorted(indices & set(graph.carriers)))
    if graph.carriers == indices and len(indices) == 1 and all(
            sort == indices[0] for position, decl in enumerate(graph.declarations)
            if decl.kind == z3.Z3_OP_UNINTERPRETED or _map_symbol(graph, position) is not None
            for sort in _symbol_signature(graph, position)[0]):
        return ()
    return indices


def _sort_family(graph, sort, family):
    """A family of the interpretation over an uninterpreted sort: elems, funs, or (index sorts only) inj.

    The sorts rendered as _m.U share _m.elems and _m.funs. A sort with a
    type of its own (_index_sorts) has its constants in _m.sK_elems, the
    functions into it in _m.sK_funs (over argument lists in _m.U, like
    every function), and the map _m.sK_inj injecting its terms into _m.U
    as arguments. Like _m.int, nothing states that the injection is
    injective and nothing needs it; a model is an instance with its own
    carrier of the sort as _m.SK, a copy of it in the disjoint union _m.U,
    and the inclusion as _m.sK_inj.
    """
    if sort in graph.index_sorts:
        return "_m.%s_%s" % (_array_type_code(graph, sort), family)
    return "_m." + family


def _index_sort_fields(graph):
    """The interpretation's fields of the sorts with a type of their own: the type, nonempty as every sort is."""
    fields = []
    for sort in graph.index_sorts:
        lean, code = _component_type(graph, sort).replace("_m.", ""), _array_type_code(graph, sort)
        fields += [(lean, "Type"), (code + "_nonempty", "Nonempty " + lean), (code + "_elems", "Nat -> " + lean),
                   (code + "_funs", "Nat -> List U -> " + lean), (code + "_inj", lean + " -> U")]
    return tuple(fields)


def _validate_graph(source, certificate):
    _fields(certificate, (
        "format", "format_version", "z3_version", "fragment", "result",
        "verification", "source_smt2", "query", "declarations", "nodes", "assertions",
        "proof", "rule_counts",
    ), "certificate")
    if (certificate["format"] != "z3-native-proof-dag"
            or type(certificate["format_version"]) is not int
            or certificate["format_version"] != 2
            or certificate["fragment"] not in _FRAGMENTS
            or certificate["result"] != "unsat"
            or certificate["verification"] != "unverified"
            or type(certificate["z3_version"]) is not str
            or not certificate["z3_version"]
            or type(certificate["query"]) is not int
            or certificate["query"] < 0):
        raise ReconstructionError("unsupported certificate header")
    if type(certificate["source_smt2"]) is not str or certificate["source_smt2"] != source:
        raise ReconstructionError("certificate source does not match the original input")
    raw_declarations = _list(certificate["declarations"], "declarations")
    sorts = _uninterpreted_sorts(raw_declarations)
    declarations = tuple(_declaration(raw, sorts) for raw in raw_declarations)
    nodes, counts = [], Counter()
    for index, raw in enumerate(_list(certificate["nodes"], "nodes")):
        _fields(raw, ("declaration", "arguments"), "node")
        declaration = _index(raw["declaration"], len(declarations), "declaration")
        decl = declarations[declaration]
        arguments = tuple(_index(arg, index, "earlier node")
                          for arg in _list(raw["arguments"], "node arguments"))
        domain = decl.domain
        if decl.kind in (z3.Z3_OP_AND, z3.Z3_OP_OR):
            domain = ("Bool",) * len(arguments)
        elif decl.kind == z3.Z3_OP_XOR and len(arguments) == 1:
            domain = ("Bool",)  # Z3 accepts (xor p) and reads it as p; see _formula_body.
        elif decl.range in _ARITH_SORTS and decl.kind in (z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_MUL):
            domain = (decl.range,) * max(len(arguments), 1)
        elif decl.range == "Bool" and decl.kind == z3.Z3_OP_DISTINCT and decl.domain[:1] not in ((), ("Bool",)):
            domain = (decl.domain[0],) * len(arguments)
        if len(arguments) != len(domain):
            raise ReconstructionError("wrong number of arguments at node %d" % index)
        for argument, expected in zip(arguments, domain):
            if declarations[nodes[argument].declaration].range != expected:
                raise ReconstructionError("wrong argument sort at node %d" % index)
        nodes.append(_Node(declaration, arguments))
        if decl.range == "Proof":
            counts[decl.name] += 1
    used = {node.declaration for node in nodes}
    if any(index not in used and set(decl.domain + (decl.range,)) & set(sorts)
           for index, decl in enumerate(declarations)):
        # The exporters apply every symbol they declare (only proof rules are
        # pre-declared), so the sort set is exactly the sorts the proof graph uses
        # and cannot be padded to match an input the certificate was not built from.
        raise ReconstructionError("unused declaration over an uninterpreted sort")
    assertions = tuple(_index(arg, len(nodes), "assertion")
                       for arg in _list(certificate["assertions"], "assertions"))
    root = _index(certificate["proof"], len(nodes), "proof")
    numeric_sorts = {decl.range for decl in declarations if decl.range in _ARITH_SORTS}
    numeric_sorts.update(sort for decl in declarations for sort in decl.domain if sort in _ARITH_SORTS)
    if any(decl.kind == z3.Z3_OP_IS_INT for decl in declarations):
        # (is_int t) states t equal to the cast of its floor, an Int term,
        # though the certificate may declare no other ((is_int 0.5) alone,
        # which the exporter classifies as mixed).
        numeric_sorts.add("Int")
    # An array over Int or Real makes the certificate arithmetic even if no
    # term of that sort occurs (the exporter classifies it so).
    numeric_sorts.update(component for sort in sorts for component in _array_components(sort) or ()
                         if component in _ARITH_SORTS)
    if len(numeric_sorts) > 1 and certificate["fragment"] not in ("qf_lira", "qf_uflira"):
        raise ReconstructionError("%s certificates cannot mix Int and Real arithmetic" % certificate["fragment"])
    arithmetic = bool(numeric_sorts)
    numeric = _MIXED if len(numeric_sorts) > 1 else numeric_sorts.pop() if numeric_sorts else "Real"
    if arithmetic and certificate["fragment"] in ("propositional", "qf_uf"):
        raise ReconstructionError("%s certificates cannot contain arithmetic" % certificate["fragment"])
    uninterpreted = bool(sorts) or any(decl.kind == z3.Z3_OP_UNINTERPRETED and decl.domain for decl in declarations)
    if uninterpreted != (certificate["fragment"] in ("qf_uf", "qf_uflra", "qf_uflia", "qf_uflira")):
        raise ReconstructionError("only qf_uf, qf_uflra, qf_uflia, and qf_uflira certificates declare an "
                                  "uninterpreted sort or function, and they must use one")
    floors = any(decl.kind in (z3.Z3_OP_TO_INT, z3.Z3_OP_IS_INT) for decl in declarations)
    graph = _Graph(declarations, tuple(nodes), assertions, root, arithmetic, sorts, uninterpreted, numeric, floors)
    if graph.fragment != certificate["fragment"]:
        if not arithmetic:
            raise ReconstructionError("%s certificates must contain arithmetic" % certificate["fragment"])
        if certificate["fragment"] in ("qf_lira", "qf_uflira"):
            raise ReconstructionError("%s certificates contain both Int and Real arithmetic" % certificate["fragment"])
        # The uninterpreted symbols agree with the label (checked above), so
        # the label names the other arithmetic sort.
        raise ReconstructionError("only qf_lia and qf_uflia certificates contain Int arithmetic alone, "
                                  "and qf_lira and qf_uflira contain both sorts")
    if graph.fragment != "propositional" and any(
            decl.kind in _PSEUDO_BOOLEAN or (decl.kind == z3.Z3_OP_PR_TH_LEMMA and decl.parameters[0] == "pb")
            for decl in declarations):
        raise ReconstructionError("pseudo-Boolean constraints occur in propositional certificates only")
    if any(graph.decl(arg).range != "Bool" for arg in assertions):
        raise ReconstructionError("assertion roots must be Boolean expressions")
    # The theorem states the assertions, so every div, mod, and rem they contain
    # must mean the same in Lean and in SMT-LIB (see _integer_divisor). A
    # proof step may mention other such terms: Z3's rewriter cancels a common
    # factor of (div (* 2 x) (- 2)) through (ite (= 0 (- 2)) (div (* 2 x) 0)
    # (div (* x 1) (- 1))), whose dead branch divides by zero. Lean checks
    # those steps under its own total division, which proves nothing about
    # the assertions beyond the theorem.
    stated = set()
    for assertion in assertions:
        stated |= _reachable(graph, assertion)[0]
    for index in sorted(stated):
        if graph.kind(index) in _DIVISION_KINDS:
            _integer_divisor(graph, index)
    if graph.decl(root).range != "Proof" or graph.kind(graph.conclusion(root)) != z3.Z3_OP_FALSE:
        raise ReconstructionError("the root must be a proof concluding false")
    reported = certificate["rule_counts"]
    if (type(reported) is not dict
            or any(type(count) is not int or count <= 0 for count in reported.values())
            or reported != dict(counts)):
        raise ReconstructionError("native rule counts do not match the proof graph")
    return graph


# Symbol tables of a certificate, by (range sort class, has arguments): Boolean
# atoms, Real or Int variables, elements of the uninterpreted sorts, functions
# into them, predicates, functions with a Real or Int result, array constants,
# and functions into arrays. Each table maps a name to its declaration.
_SYMBOL_TABLES = {
    ("Bool", False): "atoms", ("Real", False): "variables", ("Int", False): "variables", ("array", False): "arrays",
    ("sort", False): "elements", ("sort", True): "functions", ("Bool", True): "predicates",
    ("Real", True): "numeric_functions", ("Int", True): "numeric_functions", ("array", True): "array_functions",
}
_TABLE_LABELS = {
    "atoms": "Atom", "variables": "Variable", "elements": "Element", "functions": "Function",
    "predicates": "Predicate", "numeric_functions": "%s function",  # filled with the function's result sort
    "arrays": "Array", "array_functions": "Array function",
}


def _symbol_table(range_name, arity, sorts):
    if range_name in sorts:
        range_name = "array" if _array_components(range_name) else "sort"
    return _SYMBOL_TABLES.get((range_name, arity > 0))


def _sort_name(sort):
    """The certificate's name for a sort of the original input."""
    kind = sort.kind()
    if kind == z3.Z3_BOOL_SORT:
        return "Bool"
    if kind == z3.Z3_REAL_SORT:
        return "Real"
    if kind == z3.Z3_INT_SORT:
        return "Int"
    if kind == z3.Z3_ARRAY_SORT:
        return array_sort_name(sort)
    return sort.name()


def _bind_input(source, graph, fragment=None, query=0):
    """Compare exact structures using hash-consing, not a digest or solver check.

    The input is the assertion snapshot of the certificate's query, rebuilt
    from the original script (proof_certificate.query_snapshot), so the
    certificate's copy of the assertions is never trusted.
    Symbols are bound by name, so each name must denote one symbol of the input
    (Z3 accepts overloading by sort; the frontend rejects it and this check is
    repeated here) and the certificate's declaration must carry that symbol's
    full signature. Interned terms also carry their sort, so terms of different
    sorts never compare equal even though Lean renders the sorts as _m.U
    (all but those with a type of their own, _index_sorts).
    """
    context = z3.Context(proof=False)
    original, original_fragment = parse_assertions(source, context, integer=True, query=query)
    if fragment is None:
        fragment = graph.fragment
    if original_fragment != fragment:
        raise ReconstructionError("the input is in fragment %s, not %s" % (original_fragment, fragment))
    interned, terms = {}, {}
    tables = {table: {} for table in _SYMBOL_TABLES.values()}

    def intern(kind, name, range_name, children):
        key = (kind, name, range_name, tuple(children))
        return interned.setdefault(key, len(interned))

    def register(name, declaration):
        domain, range_name = _symbol_signature(graph, declaration)
        table = _symbol_table(range_name, len(domain), graph.sorts)
        if table is None:
            raise ReconstructionError("unsupported symbol signature: %s" % name)
        if name in tables[table] and (tables[table][name] != declaration if _map_symbol(graph, declaration) is None
                                      else _symbol_signature(graph, tables[table][name]) != (domain, range_name)):
            raise ReconstructionError("ambiguous %s symbol identity: %s" % (
                {"atoms": "Boolean", "variables": "arithmetic" if graph.numeric == _MIXED else graph.numeric,
                 "numeric_functions": "arithmetic function" if graph.numeric == _MIXED
                 else graph.numeric + " function"}.get(table, table[:-1]), name))
        if any(name in other for key, other in tables.items() if key != table):
            raise ReconstructionError("symbol used with two sorts: %s" % name)
        tables[table].setdefault(name, declaration)

    maps = []  # map declarations of uninterpreted functions, registered after the applied symbols
    constructors = {}  # certificate constructor name -> its sort
    for index, node in enumerate(graph.nodes):
        decl = graph.decl(index)
        if decl.range == "Proof":
            continue
        name = ""
        if decl.kind == z3.Z3_OP_UNINTERPRETED:
            name = decl.name
            register(name, node.declaration)
        elif decl.kind == z3.Z3_OP_ANUM:
            name = str(Fraction(decl.name))
        elif decl.kind in _PSEUDO_BOOLEAN:
            name = " ".join(decl.parameters)  # the bound and coefficients are part of the constraint
        elif decl.kind == z3.Z3_OP_ARRAY_MAP:
            name = " ".join(decl.parameters)  # the mapped function
            if _map_symbol(graph, node.declaration) is not None:
                maps.append(node.declaration)
        elif decl.kind in (z3.Z3_OP_DT_CONSTRUCTOR, z3.Z3_OP_DT_IS):
            # Constructors, and recognizers by their constructor, are told
            # apart by name (their interned identity), and each must be one
            # of the input's (checked below).
            name = decl.name
            sort = decl.range if decl.kind == z3.Z3_OP_DT_CONSTRUCTOR else decl.domain[0]
            if constructors.setdefault(name, sort) != sort:
                raise ReconstructionError("constructor used with two sorts: %s" % name)
        terms[index] = intern(decl.kind, name, decl.range, (terms[arg] for arg in node.arguments))
    for declaration in maps:
        # The function a map applies is a symbol of the input like an
        # applied one; if it is applied too, both must agree on its signature.
        register(_map_symbol(graph, declaration)[0], declaration)

    original_terms, original_sorts, enumerations = {}, set(), {}
    original_symbols = {table: {} for table in tables}  # name -> (domain, range)
    pending = [(expr, False) for expr in reversed(list(original))]
    while pending:
        expr, expanded = pending.pop()
        if expr.get_id() in original_terms:
            continue
        if not expanded:
            pending.append((expr, True))
            pending.extend((child, False) for child in reversed(expr.children()))
            continue
        decl, name, range_name = expr.decl(), "", _sort_name(expr.sort())
        leaves = [expr.sort()]
        if expr.sort().kind() == z3.Z3_ARRAY_SORT:
            original_sorts.update(sort for sort in _array_sort_names(range_name) if sort not in _RESERVED_SORTS)
            leaves = array_leaf_sorts(expr.sort())  # an enumeration of the elements
        for leaf in leaves:
            if is_carrier_sort(leaf):
                original_sorts.add(leaf.name())
            if is_enumeration_sort(leaf):
                enumerations[leaf.name()] = [str(constructor.name()) for constructor in enumeration_constructors(leaf)]
        parameters = map_parameters(expr) if decl.kind() == z3.Z3_OP_ARRAY_MAP else ()
        function = decl if decl.kind() == z3.Z3_OP_UNINTERPRETED else (
            decl.params()[0] if parameters[:1] == (_DECLARED_MAP,) else None)
        if function is not None:
            # An applied or mapped uninterpreted function, by its own signature.
            name = str(function.name())
            signature = (tuple(_sort_name(function.domain(i)) for i in range(function.arity())),
                         _sort_name(function.range()))
            table = _symbol_table(signature[1], function.arity(), graph.sorts)
            if table is None:
                raise ReconstructionError("certificate sort does not match the original input")
            if original_symbols[table].setdefault(name, signature) != signature:
                raise ReconstructionError("symbol declared with several signatures: %s" % name)
        elif decl.kind() == z3.Z3_OP_ANUM:
            name = str(numeral_value(expr))
        elif decl.kind() in _PSEUDO_BOOLEAN:
            name = " ".join(pseudo_boolean_parameters(decl))
        elif decl.kind() == z3.Z3_OP_DT_CONSTRUCTOR:
            name = str(decl.name())
        elif decl.kind() in RECOGNIZER_KINDS:
            name = str(decl.params()[0].name())
        if decl.kind() == z3.Z3_OP_ARRAY_MAP:
            name = " ".join(parameters)
        kind = z3.Z3_OP_DT_IS if decl.kind() in RECOGNIZER_KINDS else decl.kind()  # as the certificate writes it
        original_terms[expr.get_id()] = intern(
            kind, name, range_name, (original_terms[child.get_id()] for child in expr.children()))
    if original_sorts != set(graph.sorts):
        raise ReconstructionError("certificate sort does not match the original input")
    for name, sort in constructors.items():
        # The certificate may name constructors the assertions do not (the
        # datatype solver splits over all of them), so each is looked up in
        # the input's own declaration of its enumeration.
        if name not in enumerations.get(sort, ()):
            raise ReconstructionError("not a constructor of the input's enumeration %s: %s" % (sort, name))
        if any(name in table for table in tables.values()):
            raise ReconstructionError("symbol used with two sorts: %s" % name)
    graph.enumerations.clear()
    graph.enumerations.update(enumerations)
    for sort in graph.index_sorts:
        if sort in enumerations:
            # Its constructors and case fields are stated over _m.U. (The
            # exporter rejects arrays indexed by an enumeration.)
            raise ReconstructionError("maps, set operators, and constant arrays over arrays indexed by an "
                                      "enumeration are not supported: %s" % sort)
    if any(set(tables[table]) != set(original_symbols[table]) for table in tables):
        raise ReconstructionError("certificate assertions do not match the original input")
    for table, symbols in tables.items():
        for name, declaration in symbols.items():
            if _symbol_signature(graph, declaration) != original_symbols[table][name]:
                raise ReconstructionError("certificate symbol signature does not match the original input: %s" % name)
    if [terms[arg] for arg in graph.assertions] != [original_terms[expr.get_id()] for expr in original]:
        raise ReconstructionError("certificate assertions do not match the original input")
    return terms, tables


def _fold(operator, arguments, identity):
    if not arguments:
        return identity
    result = arguments[-1]
    for argument in reversed(arguments[:-1]):
        result = "(%s %s %s)" % (operator, argument, result)
    return result


def _formula(graph, node):
    return "(formula_%d _atoms%s)" % (node, graph.valuation)


def _term(graph, node):
    return "(term_%d _atoms%s)" % (node, graph.valuation)


def _valuation_binder(graph):
    return {"qf_lra": " (_vars : Nat -> Rat)", "qf_lia": " (_vars : Nat -> Int)",
            "qf_lira": " (_vars : Nat -> Rat) (_ivars : Nat -> Int)", "qf_uf": _UF_BINDERS,
            "qf_uflra": _UFLRA_BINDERS, "qf_uflia": _UFLIA_BINDERS,
            "qf_uflira": _UFLIRA_BINDERS}.get(graph.fragment, "")


def _interpretation_structure(graph, tables, variable_indices):
    """Declare the structure whose one argument _m interprets the uninterpreted symbols (none outside the UF fragments).

    tables and variable_indices (the symbols of the certificate and their
    indices) give the enumeration fields (_enumeration_fields).
    """
    if not graph.uninterpreted:
        return []
    fields = _UF_FIELDS + (_NUMERIC_FIELDS[graph.numeric] if graph.arithmetic else ())
    fields += _index_sort_fields(graph) + _array_family_fields(graph)
    if _carrier_inhabited(graph):
        fields += _NONEMPTY_FIELDS
    if graph.enumerations:
        fields += _enumeration_fields(graph, tables, variable_indices)
    return ["structure Interpretation where"] + ["  %s : %s" % field for field in fields] + [""]


def _carrier_inhabited(graph):
    """Whether the interpretation states that its carrier is nonempty (_NONEMPTY_FIELDS).

    It does when an extensionality witness is chosen from the carrier (_nonempty).
    A sort with a type of its own always has its own field (_index_sort_fields).
    """
    return any(decl.kind == z3.Z3_OP_ARRAY_EXT and _inhabitant_sort(decl.range) in graph.carriers
               and _inhabitant_sort(decl.range) not in graph.index_sorts for decl in graph.declarations)


def _inhabited(graph, sort):
    """Whether _nonempty has a proof for an index sort: always, except over _m.U without its nonempty field."""
    inhabitant = _inhabitant_sort(sort)
    return inhabitant not in graph.carriers or inhabitant in graph.index_sorts or _carrier_inhabited(graph)


def _enumeration_fields(graph, tables, variable_indices):
    """The fields stating what an enumeration is: distinct constructors, and every value one of them.

    The constructors of every enumeration of the input, in its declaration
    order, are the family ctors (graph.constructor_index), all of them
    whether the proof mentions them or not. enum_distinct states that two
    constructors of one enumeration differ, and for every constant of an
    enumeration sort (enum_cases_i, i its index in elems) and every
    function with an enumeration result (enum_fcases_j, over every argument
    list) that its value is one of the constructors of that sort, and for
    every array constant and function into arrays of an enumeration
    (enum_acases_i, enum_afcases_j) that each of its reads is. A model of
    the input is still an instance (see _UF_FIELDS): the enumeration's values
    join the disjoint union _m.U as the constructors' own values, a
    function is valued outside its domain by a constructor of its range, and
    an array outside its index sort by a constructor of its elements. The
    statement is about the input's symbols only, so it is as strong as the
    input's datatype declarations and no stronger.
    """
    fields, offset, pairs = [("ctors", "Nat -> U")], 0, []
    for sort in sorted(graph.enumerations):
        count = len(graph.enumerations[sort])
        pairs.extend("(Not (ctors %d = ctors %d))" % (offset + i, offset + j)
                     for i in range(count) for j in range(i + 1, count))
        offset += count
    if pairs:
        fields.append(("enum_distinct", _fold("And", pairs, "True")))
    for table, field in (("elements", "enum_cases"), ("functions", "enum_fcases"), ("arrays", "enum_acases"),
                         ("array_functions", "enum_afcases")):
        for _, declaration in sorted(tables[table].items(), key=lambda item: variable_indices[item[1]]):
            sort, index = graph.declarations[declaration].range, variable_indices[declaration]
            binder, applied = "forall _args : List U, " if table.endswith("functions") else "", ""
            if table.startswith("array"):
                # Every read of an array constant or a function's array value
                # (at every index, the model's arrays extended by a
                # constructor outside their index sort, see _array_injection).
                if not _enumeration_array(graph, sort):
                    continue
                family = _array_functions(graph, sort) if binder else _array_family(graph, sort)
                binder += "forall _i : %s, " % _array_types(graph, sort)[0].replace("_m.", "")
                applied, sort = "%s %d%s _i" % (family, index, " _args" if "_args" in binder else ""), \
                    _array_components(sort)[1]
            elif sort in graph.enumerations:
                applied = "funs %d _args" % index if binder else "elems %d" % index
            else:
                continue
            fields.append(("%s_%d" % (field, index), binder + _enumeration_cases(graph, sort, applied, "ctors")))
    return tuple(fields)


def _enumeration_array(graph, sort):
    """Whether a certificate sort name is an array sort whose elements are one of the input's enumerations."""
    components = _array_components(sort)
    return bool(components) and components[1] in graph.enumerations


def _enumeration_cases(graph, sort, value, constructors="_m.ctors"):
    """The Lean proposition that value is one of the constructors of the enumeration sort."""
    return _fold("Or", ["(%s = %s %d)" % (value, constructors, graph.constructor_index(constructor, sort))
                        for constructor in graph.enumerations[sort]], "False")


def _enumeration_helpers(graph, reachable, atom_indices, variable_indices, folded=False):
    """State the enumeration facts a theory step over enumeration terms needs: the fields, instantiated.

    grind knows nothing about the constructors: it gets their distinctness
    and, for every constant and application of an enumeration sort the step
    reaches, the disjunction of its possible values, on which it splits.
    With folded, the facts of applications with arguments are left to
    _folded_enumeration_cases.
    """
    nodes = [node for node in sorted(reachable)
             if graph.is_term(node) and graph.decl(node).range in graph.enumerations]
    if not nodes:
        return []
    helpers = []
    if any(len(constructors) > 1 for constructors in graph.enumerations.values()):
        helpers.append("  have _ed := _m.enum_distinct")

    def child(sub):
        return "(%s)" % _inline(graph, sub, atom_indices, variable_indices)

    for node in nodes:
        if graph.kind(node) in (z3.Z3_OP_SELECT, z3.Z3_OP_ARRAY_DEFAULT):
            proof = _read_cases(graph, node, child, variable_indices)
            if proof is not None:
                helpers.append("  have _ec%d : %s := %s" % (
                    node, _enumeration_cases(graph, graph.decl(node).range, child(node)), proof))
            continue
        if graph.kind(node) != z3.Z3_OP_UNINTERPRETED:
            continue
        index = variable_indices[graph.nodes[node].declaration]
        if graph.arguments(node):
            if folded:
                continue
            helpers.append("  have _ec%d := _m.enum_fcases_%d %s" % (
                node, index, _application_arguments(graph, graph.arguments(node), child, child)))
        else:
            helpers.append("  have _ec%d := _m.enum_cases_%d" % (node, index))
    return helpers


def _folded_enumeration_cases(graph, reachable, variable_indices):
    """The enumeration cases of _enumeration_helpers for applications, over their definitions, folded.

    Returns the have lines, their names, and the applications' arguments, for
    _grind_lemma to revert before its unfold as it does the ite gates
    (_folded_ite_gates). Written out, the argument list of an application
    over nested ites repeats every inner ite in full: two eight-level
    chains of Color ites through f and g (enumeration_chain_instance(8))
    took 26.7 MB of such facts, and in an euf lemma, whose ites stay folded
    in the goal, the written-out fact did not even meet the goal's term.
    The field is applied to the application's argument list as its
    definition writes it (_term_body), over the arguments' definitions,
    which the unfold rewrites as it rewrites the goal's.
    """
    lines, names, nodes = [], [], set()
    for node in sorted(reachable):
        if (not graph.is_term(node) or graph.kind(node) != z3.Z3_OP_UNINTERPRETED or not graph.arguments(node)
                or graph.decl(node).range not in graph.enumerations):
            continue
        lines.append("have _ec%d := _m.enum_fcases_%d %s" % (
            node, variable_indices[graph.nodes[node].declaration], _application_arguments(
                graph, graph.arguments(node), lambda term: _term(graph, term),
                lambda formula: _formula(graph, formula))))
        names.append("_ec%d" % node)
        # The definitions the fact mentions: the application's own may be
        # unfolded in the goal already (outside the atoms of an Int lemma,
        # see _grind_lemma), and unfold rejects a name that does not occur.
        nodes.update(graph.arguments(node))
    return lines, names, nodes


def _read_cases(graph, node, child, variable_indices):
    """A Lean proof that an enumeration-valued node is one of its sort's constructors, or None.

    Constants and applications have their fields, a constructor is one,
    an ite is one if both branches are (_cases_ite), and a read (select a j)
    is one by the cases of the reads at j of what a may evaluate to: an
    array constant or application (enum_acases_i, enum_afcases_j), the
    array and the stored value of a store (_cases_store), both branches of
    an ite, and the value of a constant array (_cases_const). A default
    value (default a) is one by the value of a constant array
    (_cases_default_const), the default of the array a store writes into
    (_cases_default_store), or those of both branches of an ite. Any other
    array gives None (the default value of an array constant or
    application, which no field covers), and so does every default value
    read at a generic index (_Graph.generic); the lemma is left to grind
    without the fact.

    The walk is on an explicit stack (a goal is ("value", node), ("read",
    array, index), or ("default", array)), so a store chain deeper than Python's recursion limit
    gets its proof like any other (see test_proof_to_lean_deep.py), and a
    goal two paths share is proved once.
    """
    sort = graph.decl(node).range
    proofs = {}
    root = ("value", node)
    pending = [root]
    while pending:
        goal = pending[-1]
        if goal in proofs:
            pending.pop()
            continue
        subgoals = _read_cases_subgoals(graph, goal)
        missing = [subgoal for subgoal in subgoals if subgoal not in proofs]
        if missing:
            pending.extend(reversed(missing))
            continue
        pending.pop()
        parts = [proofs[subgoal] for subgoal in subgoals]
        proofs[goal] = None if None in parts else _read_cases_proof(graph, goal, parts, sort, child,
                                                                     variable_indices)
    return proofs[root]


def _read_cases_subgoals(graph, goal):
    """The goals whose proofs the proof of goal is built from (_read_cases)."""
    kind, arguments = graph.kind(goal[1]), graph.arguments(goal[1])
    if goal[0] == "value":
        if kind == z3.Z3_OP_ITE:
            return [("value", branch) for branch in arguments[1:]]
        if kind == z3.Z3_OP_SELECT:
            return [("read", arguments[0], arguments[1])]
        if kind == z3.Z3_OP_ARRAY_DEFAULT:
            return [("default", arguments[0])]
        return []
    if kind == z3.Z3_OP_CONST_ARRAY:
        return [("value", arguments[0])]
    if kind == z3.Z3_OP_STORE:
        return [(goal[0], arguments[0]) + goal[2:]] + ([("value", arguments[2])] if goal[0] == "read" else [])
    if kind == z3.Z3_OP_ITE:
        return [(goal[0], branch) + goal[2:] for branch in arguments[1:]]
    return []


def _read_cases_proof(graph, goal, parts, sort, child, variable_indices):
    """The proof of goal from the proofs parts of its subgoals, or None (_read_cases)."""
    node = goal[1]
    kind, arguments = graph.kind(node), graph.arguments(node)
    cases = "(fun _x : _m.U => %s)" % _enumeration_cases(graph, sort, "_x")
    if goal[0] == "value":
        if kind == z3.Z3_OP_DT_CONSTRUCTOR:
            position = graph.enumerations[sort].index(graph.decl(node).name)
            last = position == len(graph.enumerations[sort]) - 1
            return "(%s%s%s)" % ("Or.inr (" * position, "rfl" if last else "Or.inl rfl", ")" * position)
        if kind == z3.Z3_OP_UNINTERPRETED:
            index = variable_indices[graph.nodes[node].declaration]
            if arguments:
                return "(_m.enum_fcases_%d %s)" % (index, _application_arguments(graph, arguments, child, child))
            return "_m.enum_cases_%d" % index
        if kind == z3.Z3_OP_ITE:
            return "(_cases_ite %s %s _ %s %s %s %s)" % (cases, child(arguments[0]), child(arguments[1]),
                                                         child(arguments[2]), parts[0], parts[1])
        if kind in (z3.Z3_OP_SELECT, z3.Z3_OP_ARRAY_DEFAULT):
            return parts[0]
        return None
    index_type = _array_types(graph, graph.decl(node).range)[0]
    if goal[0] == "default":
        if graph.generic or _array_components(graph.decl(node).range)[0] not in _UNBOUNDED:
            return None  # No _default over this index sort (the exporter rejects it), or no such theorem.
        if kind == z3.Z3_OP_CONST_ARRAY:
            return "(_cases_default_const %s %s %s %s)" % (cases, _unbounded(graph, node, explicit=True),
                                                           child(arguments[0]), parts[0])
        if kind == z3.Z3_OP_STORE:
            return "(_cases_default_store %s %s %s %s %s %s)" % (
                cases, _unbounded(graph, node), child(arguments[0]), child(arguments[1]), child(arguments[2]),
                parts[0])
        if kind == z3.Z3_OP_ITE:
            default = "(fun _a : %s -> _m.U => %s)" % (index_type, _enumeration_cases(
                graph, sort, "_default %s _a" % _unbounded(graph, node)))
            return "(_cases_ite %s %s _ %s %s %s %s)" % (default, child(arguments[0]), child(arguments[1]),
                                                         child(arguments[2]), parts[0], parts[1])
        return None
    read = goal[2]
    if kind == z3.Z3_OP_CONST_ARRAY:
        return "(_cases_const %s %s %s %s)" % (cases, child(arguments[0]), child(read), parts[0])
    if kind == z3.Z3_OP_UNINTERPRETED:
        index = variable_indices[graph.nodes[node].declaration]
        if arguments:
            return "(_m.enum_afcases_%d %s %s)" % (
                index, _application_arguments(graph, arguments, child, child), child(read))
        return "(_m.enum_acases_%d %s)" % (index, child(read))
    if kind == z3.Z3_OP_STORE:
        return "(_cases_store %s %s %s %s %s %s %s)" % (
            cases, child(arguments[0]), child(arguments[1]), child(arguments[2]), child(read), parts[0], parts[1])
    if kind == z3.Z3_OP_ITE:
        selected = "(fun _a : %s -> _m.U => %s)" % (index_type, _enumeration_cases(
            graph, sort, "_select _a %s" % child(read)))
        return "(_cases_ite %s %s _ %s %s %s %s)" % (selected, child(arguments[0]), child(arguments[1]),
                                                     child(arguments[2]), parts[0], parts[1])
    return None


def _infix(operator, arguments):
    result = arguments[0]
    for argument in arguments[1:]:
        result = "(%s %s %s)" % (result, operator, argument)
    return result


def _application_arguments(graph, arguments, term, formula):
    """Render the argument list of a function or predicate over the uninterpreted sorts.

    A Boolean argument is injected into the carrier by _m.bool (its formula is
    rendered as a Prop), a Real or Int one by _m.real or _m.int, an array by
    the injection of its Lean type (_array_injection), and a term of a sort
    with a type of its own by that sort's (_sort_family).
    """
    return "[%s]" % ", ".join("(%s %s)" % (graph.injection(arg), term(arg)) if graph.is_arith(arg)
                              else "(_m.%s %s)" % (_array_injection(graph, graph.decl(arg).range), term(arg))
                              if graph.is_array(arg)
                              else "(%s %s)" % (_sort_family(graph, graph.decl(arg).range, "inj"), term(arg))
                              if graph.decl(arg).range in graph.index_sorts
                              else term(arg) if graph.is_term(arg)
                              else "(_m.bool %s)" % formula(arg) for arg in arguments)


def _numeral(sort, value):
    """Render a rational as a literal of the arithmetic sort (Real or Int); Int numerals are integers."""
    if value.denominator == 1:
        return "((%d : %s))" % (value.numerator, _NUMBER_TYPES[sort])
    if sort == "Int":
        raise ReconstructionError("fractional value in an Int term: %s" % value)
    return "((%d : Rat) / (%d : Rat))" % (value.numerator, value.denominator)


def _variable(graph, node, index):
    """Render an arithmetic variable: _ivars for an Int one in a qf_lira certificate, _vars otherwise."""
    return ("_ivars %d" if graph.numeric == _MIXED and graph.is_int(node) else "_vars %d") % index


def _negation(graph, node, rendered):
    """Render the negation of a rendered arithmetic node: 0 - t over Int, -t over Real and of a positive Int numeral.

    Lean's grind takes the Int term -0 for a numeral other than 0 (a
    negated literal is its normal form of a negative numeral), and the
    kernel rejects the proof it builds on that (application type mismatch
    at decide (-0 = 0) = false), an error that comes after the tactic
    block, where no alternative of first catches it. grind meets -0
    whenever its simplifier evaluates the negated term to the literal 0 in
    an argument of an uninterpreted application, a read, or a store: (f (-
    0)), (select a (- (* 0 x))), (p (- (mod x 1))), (f (- (ite true 0
    1))). Which terms the simplifier evaluates to 0 is its business (a
    remainder by 1, an ite with a decided condition), so every Int
    negation is the difference 0 - t, the same number, which the
    simplifier evaluates with t and otherwise normalizes to -t. Only the
    negation of a positive numeral keeps the form of a negative numeral
    ((- 2) is -2). Rat has no such defect.
    """
    if _negated_as_difference(graph, node):
        return "(%s - %s)" % (_numeral("Int", Fraction(0)), rendered)
    return "(-%s)" % rendered


def _negated_as_difference(graph, node):
    """Whether the negation of a node is rendered as a difference: an Int node other than a positive numeral."""
    return graph.is_int(node) and not (graph.kind(node) == z3.Z3_OP_ANUM and Fraction(graph.decl(node).name) > 0)


def _negative_quotient(graph, node):
    """Whether an Int node is a div by a negative constant, rendered as 0 - t / (0 - d) for the divisor d.

    Lean's simplifier rewrites the quotient t / -k to -(t / k), which is
    the literal -0 of _negation when t / k evaluates to 0 ((div 2 (- 5)),
    (div (mod x 1) (- 3))). The difference is the same number: the
    definition is followed by a theorem that it equals the quotient by d
    (_quotient_theorem), so the kernel checks the identity the rendering
    rests on. A div by a zero or nonconstant divisor (in a dead branch of
    a legacy proof, see _integer_divisor) keeps Lean's operator.
    """
    if graph.kind(node) != z3.Z3_OP_IDIV:
        return False
    terms = {}
    try:
        divisor = _linear_term(graph, graph.arguments(node)[1], Fraction(1), terms)
    except ReconstructionError:
        return False
    return not terms and divisor < 0


# The identity behind the rendering of a div by a negative constant
# (_negative_quotient), stated once for the theorems of the definitions.
_NEGATIVE_QUOTIENT_LEMMA = [
    "private theorem _div_neg (t d : Int) : ((0 : Int)) - t / (((0 : Int)) - d) = t / d := by",
    "  rw [Int.zero_sub d, Int.ediv_neg, Int.zero_sub, Int.neg_neg]",
]


def _quotient_theorem(graph, node, signature):
    """The theorem that the definition of a div by a negative constant is Lean's Euclidean quotient of its operands."""
    dividend, divisor = graph.arguments(node)
    return "theorem term_%d_quotient %s : %s = (%s / %s) := _div_neg _ _" % (
        node, signature, _term(graph, node), _term(graph, dividend), _term(graph, divisor))


def _term_body(graph, node, variable_indices, term=None, formula=None):
    """Render an arithmetic or uninterpreted-sort node; term and formula render its children.

    variable_indices numbers the arithmetic variables, the elements, the
    functions, and the functions with an arithmetic result, each from zero;
    the defaults render children by definition name.
    """
    term = (lambda child: _term(graph, child)) if term is None else term
    formula = (lambda child: _formula(graph, child)) if formula is None else formula
    kind = graph.kind(node)
    arguments = graph.arguments(node)
    if kind == z3.Z3_OP_UNINTERPRETED:
        index = variable_indices[graph.nodes[node].declaration]
        if not arguments and graph.decl(node).range in graph.arrays:
            return "_m.%s %d" % (_array_family(graph, graph.decl(node).range), index)
        if not arguments:
            return (_variable(graph, node, index) if graph.is_arith(node)
                    else "%s %d" % (_sort_family(graph, graph.decl(node).range, "elems"), index))
        return "%s %d %s" % (graph.function_family(node), index,
                             _application_arguments(graph, arguments, term, formula))
    if kind == z3.Z3_OP_ANUM:
        return _numeral(graph.decl(node).range, Fraction(graph.decl(node).name))
    if kind == z3.Z3_OP_DT_CONSTRUCTOR:
        return "_m.ctors %d" % graph.constructor_index(graph.decl(node).name, graph.decl(node).range)
    if kind == z3.Z3_OP_ITE:
        # The instance's proposition is inferred from the condition.
        return "(@ite %s %s (Classical.propDecidable _) %s %s)" % (
            graph.lean_type(node), formula(arguments[0]), term(arguments[1]), term(arguments[2]))
    # The value of a store or constant array with Bool elements is a formula.
    args = [term(arg) if graph.is_term(arg) else formula(arg) for arg in arguments]
    if kind == z3.Z3_OP_SELECT:
        return "(_select %s %s)" % tuple(args)
    if kind == z3.Z3_OP_STORE:
        return "(_store %s %s %s)" % tuple(args)
    if kind == z3.Z3_OP_ARRAY_EXT:
        return "(_array_diff %s %s %s)" % ((_nonempty(graph, graph.decl(node).range),) + tuple(args))
    if kind == z3.Z3_OP_CONST_ARRAY:
        return "(@_const_array %s %s %s)" % (_array_types(graph, graph.decl(node).range) + (args[0],))
    if kind == z3.Z3_OP_ARRAY_DEFAULT:
        return "(_default %s %s)" % (_unbounded(graph, arguments[0]), args[0])
    function = _set_function(graph, node)
    if function is not None:
        return "(_map%d %s %s)" % (len(args), function, " ".join(args))
    if kind == z3.Z3_OP_UMINUS:
        return _negation(graph, arguments[0], args[0])
    if kind == z3.Z3_OP_TO_REAL:
        return "((%s : Int) : Rat)" % args[0]
    if kind == z3.Z3_OP_TO_INT:
        return "(Rat.floor %s)" % args[0]
    if kind == z3.Z3_OP_ABS:
        # SMT-LIB's definition; the instance's proposition is inferred from the condition.
        return "(@ite %s (%s >= ((0 : %s))) (Classical.propDecidable _) %s %s)" % (
            graph.number_type_of(node), args[0], graph.number_type_of(node), args[0],
            _negation(graph, arguments[0], args[0]))
    if _negative_quotient(graph, node):
        zero = _numeral("Int", Fraction(0))
        return "(%s - (%s / (%s - %s)))" % (zero, args[0], zero, args[1])
    if kind in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD):
        return "(%s %s %s)" % (args[0], "/" if kind == z3.Z3_OP_IDIV else "%", args[1])
    if kind == z3.Z3_OP_REM:
        # Z3's (ite (>= k 0) (mod t k) (- (mod t k))) at the numeral divisor k.
        remainder = "(%s %% %s)" % (args[0], args[1])
        return remainder if _integer_divisor(graph, node) > 0 else _negation(graph, node, remainder)
    return _infix(_REAL_NAMES[kind], args)


def _formula_body(graph, node, atom_indices, term=None, formula=None):
    """Render a Bool node; term and formula render its children (defaults: by definition name).

    atom_indices numbers the Boolean atoms and the predicates, each from zero.
    """
    term = (lambda child: _term(graph, child)) if term is None else term
    formula = (lambda child: _formula(graph, child)) if formula is None else formula
    kind = graph.kind(node)
    arguments = graph.arguments(node)
    if kind == z3.Z3_OP_DT_IS:
        # SMT-LIB's recognizer of a nullary constructor c: (= t c).
        return "(%s = _m.ctors %d)" % (term(arguments[0]),
                                       graph.constructor_index(graph.decl(node).name, graph.decl(node).domain[0]))
    if kind == z3.Z3_OP_UNINTERPRETED and arguments:
        return "_m.preds %d %s" % (atom_indices[graph.nodes[node].declaration],
                                   _application_arguments(graph, arguments, term, formula))
    if kind in (z3.Z3_OP_SELECT, z3.Z3_OP_ARRAY_DEFAULT, z3.Z3_OP_ARRAY_EXT):
        # A read or the default value of an array with Bool elements (I ->
        # Prop), or the extensionality witness of two arrays with Bool
        # indices (Prop -> E).
        return _term_body(graph, node, None, term, formula)
    if arguments and graph.is_term(arguments[0]):
        args = [term(arg) for arg in arguments]
        if kind in _ARITH_PREDICATE_NAMES and graph.is_arith(arguments[0]):
            return "(%s %s %s)" % (args[0], _ARITH_PREDICATE_NAMES[kind], args[1])
        if kind == z3.Z3_OP_EQ:
            return "(%s = %s)" % tuple(args)
        if kind == z3.Z3_OP_IS_INT:
            # SMT-LIB's definition, (= (to_real (to_int t)) t).
            return "(((Rat.floor %s : Int) : Rat) = %s)" % (args[0], args[0])
        if kind == z3.Z3_OP_SET_SUBSET:
            # Every member of the first set is one of the second (_SUBSET_DEFINITION).
            return "(_subset %s %s)" % tuple(args)
        if kind == z3.Z3_OP_DISTINCT:
            pairs = ["(Not (%s = %s))" % (left, right)
                     for index, left in enumerate(args) for right in args[index + 1:]]
            return _fold("And", pairs, "True")
        raise ReconstructionError("unsupported arithmetic atom")
    if kind in _PSEUDO_BOOLEAN:
        return _pseudo_boolean_body(graph, node, formula)
    args = [formula(arg) for arg in arguments]
    if kind == z3.Z3_OP_UNINTERPRETED:
        return "_atoms %d" % atom_indices[graph.nodes[node].declaration]
    if kind == z3.Z3_OP_TRUE:
        return "True"
    if kind == z3.Z3_OP_FALSE:
        return "False"
    if kind == z3.Z3_OP_NOT:
        return "(Not %s)" % args[0]
    if kind == z3.Z3_OP_AND:
        return _fold("And", args, "True")
    if kind == z3.Z3_OP_OR:
        return _fold("Or", args, "False")
    if kind == z3.Z3_OP_IMPLIES:
        return "(%s -> %s)" % tuple(args)
    if kind in (z3.Z3_OP_EQ, z3.Z3_OP_IFF):
        return "(Iff %s %s)" % tuple(args)
    if kind == z3.Z3_OP_XOR:
        if len(args) == 1:
            # Z3's parser accepts a one-argument xor (its n-ary xor is
            # binarized, so one and two are the only arities) and its
            # rewriter reads it as the argument itself (bool_rewriter,
            # OP_XOR with one argument), which the legacy core records as
            # the rewrite (= (xor p) p); the parity reading agrees.
            return args[0]
        return "(Or (And %s (Not %s)) (And (Not %s) %s))" % (args[0], args[1], args[0], args[1])
    if kind == z3.Z3_OP_ITE:
        return "(Or (And %s %s) (And (Not %s) %s))" % (args[0], args[1], args[0], args[2])
    if kind == z3.Z3_OP_DISTINCT:
        pairs = ["(Not (Iff %s %s))" % (left, right)
                 for index, left in enumerate(args) for right in args[index + 1:]]
        return _fold("And", pairs, "True")
    raise ReconstructionError("unsupported Boolean expression")


def _pseudo_boolean_literal(graph, node):
    """Whether a node is a Boolean variable or a negation of one, the arguments a pseudo-Boolean constraint takes."""
    if graph.kind(node) == z3.Z3_OP_NOT:
        node = graph.arguments(node)[0]
    return graph.kind(node) == z3.Z3_OP_UNINTERPRETED and not graph.arguments(node)


def _pseudo_boolean_body(graph, node, formula):
    """Render a pseudo-Boolean constraint as an Int comparison of the weighted 0/1 values of its literals.

    Each argument, a Boolean variable or a negation of one, is valued by the
    classical (if l then 1 else 0); Lean's proofs read a negation's value as
    one minus its variable's (_PSEUDO_BOOLEAN_LEMMAS).
    """
    _, relation, weighted = _PSEUDO_BOOLEAN[graph.kind(node)]
    parameters = [int(parameter) for parameter in graph.decl(node).parameters]
    arguments = graph.arguments(node)
    coefficients = parameters[1:] if weighted else [1] * len(arguments)
    summands = []
    for coefficient, argument in zip(coefficients, arguments):
        if not _pseudo_boolean_literal(graph, argument):
            raise ReconstructionError("pseudo-Boolean arguments must be Boolean variables or their negations")
        value = "(@ite Int %s (Classical.propDecidable _) 1 0)" % formula(argument)
        summands.append(value if coefficient == 1 else "(%s * %s)" % (_numeral("Int", Fraction(coefficient)), value))
    total = _infix("+", summands) if summands else "((0 : Int))"
    return "(%s %s %s)" % (total, relation, _numeral("Int", Fraction(parameters[0])))


# The value facts of a pseudo-Boolean step, stated once per certificate that
# has one: a variable's 0/1 value lies between 0 and 1 and is 1 exactly when
# the variable holds, and a negation's value is one minus the variable's.
# Bounds rather than the disjunction (= 0 or = 1): omega splits a disjunction,
# and sixteen of them took 83 s where the bounds take none.
_PSEUDO_BOOLEAN_LEMMAS = """
private theorem _pb_bit (p : Prop) :
    (0 <= (@ite Int p (Classical.propDecidable p) 1 0) /\\ (@ite Int p (Classical.propDecidable p) 1 0) <= 1)
      /\\ (p <-> (@ite Int p (Classical.propDecidable p) 1 0) = 1) := by
  by_cases _h : p <;> simp [_h]

private theorem _pb_not (p : Prop) :
    (@ite Int (Not p) (Classical.propDecidable (Not p)) 1 0) = 1 - (@ite Int p (Classical.propDecidable p) 1 0) := by
  by_cases _h : p <;> simp [_h]
""".strip("\n").split("\n")


def _pseudo_boolean_lemma(graph, node, prefix, atom_indices):
    """Prove a step over pseudo-Boolean constraints by integer arithmetic over the variables' 0/1 values.

    The step is a th-lemma pb (theory_pb's propagation, conflict, or axiom
    clause, stated as the implication from its premises like every legacy
    th-lemma) or a rewrite between constraints (Z3's pseudo-Boolean rewriter
    normalizes them, say (at-most 1 a b c) to (at-least 2 (not a) (not b)
    (not c))). After unfolding, every negation's value becomes one minus its
    variable's (_pb_not), each variable's value is generalized to an Int
    _x with 0 <= _x <= 1, the variable itself is rewritten to (_x = 1), and
    omega, complete for linear integer arithmetic, decides the resulting
    formula. Every node of the step must be a constraint, a Boolean variable,
    a negation, a disjunction, or false, which is all theory_pb states.
    """
    conclusion = graph.conclusion(node)
    premises = graph.arguments(node)[:-1]
    conclusions = [graph.conclusion(premise) for premise in premises] + [conclusion]
    reachable = set()
    for formula in conclusions:
        reachable |= _reachable(graph, formula)[0]
    allowed = _PSEUDO_BOOLEAN.keys() | {z3.Z3_OP_UNINTERPRETED, z3.Z3_OP_NOT, z3.Z3_OP_OR, z3.Z3_OP_FALSE}
    if prefix == "rewrite":
        allowed |= {z3.Z3_OP_EQ, z3.Z3_OP_IFF, z3.Z3_OP_AND, z3.Z3_OP_TRUE}
    if any(graph.kind(formula) not in allowed or graph.is_term(formula) for formula in reachable):
        raise ReconstructionError("pseudo-Boolean step over other formulas at node %d" % node)
    atoms = sorted(atom_indices[graph.nodes[formula].declaration] for formula in reachable
                   if graph.kind(formula) == z3.Z3_OP_UNINTERPRETED)
    lines = [
        "",
        "set_option maxHeartbeats 1000000 in",
        # Not every variable occurs outside the constraints, whose values are generalized first.
        "set_option linter.unusedSimpArgs false in",
        "private theorem %s_%d (_atoms : Nat -> Prop)" % (prefix, node),
        "    : %s := by" % " -> ".join(_formula(graph, formula) for formula in conclusions),
        "  unfold " + " ".join(_definition_names(graph, reachable)),
    ]
    if any(graph.kind(formula) == z3.Z3_OP_NOT and graph.kind(parent) in _PSEUDO_BOOLEAN
           for parent in reachable for formula in graph.arguments(parent)):
        lines.append("  (try simp only [_pb_not])")
    for atom in atoms:
        value = "(@ite Int (_atoms %d) (Classical.propDecidable (_atoms %d)) 1 0)" % (atom, atom)
        lines.extend([
            "  have _r%d := (_pb_bit (_atoms %d)).1" % (atom, atom),
            "  have _e%d := (_pb_bit (_atoms %d)).2" % (atom, atom),
            "  generalize %s = _x%d at _r%d _e%d |-" % (value, atom, atom, atom),
        ])
    # omega reads the connectives of a goal except Iff, and neither False as a
    # hypothesis nor True as a goal: a rewrite's two directions are proved
    # apart, and one to false or true is closed by those constants.
    decide = "omega" if prefix != "rewrite" else (
        "first | omega | (constructor <;> intro _h <;> first | omega | exact False.elim _h | trivial)")
    if atoms:
        lines.append("  (try simp only [%s]) <;> %s" % (", ".join("_e%d" % atom for atom in atoms), decide))
    else:
        lines.append("  " + decide)
    return lines, "(%s_%d _atoms%s)" % (prefix, node, "".join(" _step_%d" % premise for premise in premises))


def _inject(position, count, term):
    if position < count - 1:
        term = "(Or.inl %s)" % term
    for _ in range(position):
        term = "(Or.inr %s)" % term
    return term


def _project(position, count, term):
    for _ in range(position):
        term = "(And.right %s)" % term
    return "(And.left %s)" % term if position < count - 1 else term


def _select(position, count, name):
    """Project a conjunct from a let-bound name or binder of a right-nested conjunction.

    Field notation elaborates inside out: each projection starts from the
    known (unfolded) type of the name, with no metavariable per level. The
    equivalent And.left/And.right application elaborates outside in through
    one metavariable pair per level, which made and-elim over a conjunction
    of 200 operands take over half a minute.
    """
    return name + ".2" * position + (".1" if position < count - 1 else "")


def _balanced(operator, arguments, identity):
    """Nest a binary operator as a balanced tree, the left half before the right."""
    if not arguments:
        return identity
    if len(arguments) == 1:
        return arguments[0]
    middle = (len(arguments) + 1) // 2
    return "(%s %s %s)" % (operator, _balanced(operator, arguments[:middle], identity),
                           _balanced(operator, arguments[middle:], identity))


def _balanced_select(position, count, name):
    """Project a conjunct of a balanced conjunction (_balanced) by field notation.

    The outlined proof steps receive the assertions as one conjunction, Inputs.
    Right-nested, the last of 1,211 assertions sat under 1,210 projections,
    and elaborating such a chain against the unfolded definition exhausted
    maxHeartbeats; balanced, every assertion is at most log2(count) levels down.
    """
    path = ""
    while count > 1:
        middle = (count + 1) // 2
        if position < middle:
            path, count = path + ".1", middle
        else:
            path, position, count = path + ".2", position - middle, count - middle
    return name + path


def _modus_ponens(graph, terms, node):
    premise, implication, conclusion = graph.arguments(node)
    relation = graph.conclusion(implication)
    kind = graph.kind(relation)
    if kind not in (z3.Z3_OP_IMPLIES, z3.Z3_OP_EQ, z3.Z3_OP_IFF):
        raise ReconstructionError("mp requires an implication or Boolean equivalence at node %d" % node)
    antecedent, consequent = graph.arguments(relation)
    if graph.is_term(antecedent):
        raise ReconstructionError("mp requires an implication or Boolean equivalence at node %d" % node)
    if (terms[graph.conclusion(premise)] != terms[antecedent]
            or terms[conclusion] != terms[consequent]):
        raise ReconstructionError("incorrect mp antecedent or conclusion at node %d" % node)
    if kind == z3.Z3_OP_IMPLIES:
        return "(_step_%d _step_%d)" % (implication, premise)
    return "(Iff.mp _step_%d _step_%d)" % (implication, premise)


def _equivalence(graph, formula, rule):
    """Return the two sides of a Boolean equivalence or of an equality between terms.

    Boolean equivalences are Lean Iff, term equalities Lean Eq; the two never
    mix (the graph is checked to be well-sorted), so a rule's Lean term is
    chosen by the sort of the sides.
    """
    if graph.kind(formula) not in (z3.Z3_OP_EQ, z3.Z3_OP_IFF):
        raise ReconstructionError("%s requires an equivalence or equality at node %d" % (rule, formula))
    return graph.arguments(formula)


def _relation(graph, side):
    """The Lean namespace of refl, symm, and trans for sides of this sort."""
    return "Eq" if graph.is_term(side) else "Iff"


def _side(graph, side):
    return _term(graph, side) if graph.is_term(side) else _formula(graph, side)


def _equivalence_step(graph, terms, node):
    rule = graph.decl(node).name
    left, right = _equivalence(graph, graph.conclusion(node), rule)
    premises = graph.arguments(node)[:-1]
    relation = _relation(graph, left)
    if graph.kind(node) == z3.Z3_OP_PR_REFLEXIVITY:
        valid = terms[left] == terms[right]
        term = "(%s.refl %s)" % (relation, _side(graph, left))
    elif graph.kind(node) == z3.Z3_OP_PR_SYMMETRY:
        first, second = _equivalence(graph, graph.conclusion(premises[0]), rule)
        valid = terms[left] == terms[second] and terms[right] == terms[first]
        term = "(%s.symm _step_%d)" % (relation, premises[0])
    else:
        first, middle = _equivalence(graph, graph.conclusion(premises[0]), rule)
        other_middle, last = _equivalence(graph, graph.conclusion(premises[1]), rule)
        valid = (terms[left] == terms[first] and terms[middle] == terms[other_middle]
                 and terms[right] == terms[last])
        term = "(%s.trans _step_%d _step_%d)" % ((relation,) + tuple(premises))
    if not valid:
        raise ReconstructionError("incorrect %s premises or conclusion at node %d" % (rule, node))
    return term


def _commutativity(graph, terms, node):
    """(= (f a b) (f b a)) for a commutative head: equality, equivalence, and, or, xor."""
    left, right = _equivalence(graph, graph.conclusion(node), "commutativity")
    kind, arguments = graph.kind(left), graph.arguments(left)
    if (graph.nodes[left].declaration != graph.nodes[right].declaration or len(arguments) != 2
            or [terms[arg] for arg in graph.arguments(right)] != [terms[arg] for arg in reversed(arguments)]):
        raise ReconstructionError("commutativity requires one binary application with swapped arguments at node %d"
                                  % node)
    if kind == z3.Z3_OP_EQ and graph.is_term(arguments[0]):
        return "(Iff.intro Eq.symm Eq.symm)"
    if kind in (z3.Z3_OP_EQ, z3.Z3_OP_IFF):
        return "(Iff.intro Iff.symm Iff.symm)"
    if kind == z3.Z3_OP_AND:
        direction = "(fun _h => And.intro (And.right _h) (And.left _h))"
        return "(Iff.intro %s %s)" % (direction, direction)
    if kind == z3.Z3_OP_OR:
        direction = "(fun _h => Or.elim _h Or.inr Or.inl)"
        return "(Iff.intro %s %s)" % (direction, direction)
    if kind == z3.Z3_OP_XOR:
        # xor is (p and not q) or (not p and q); swapping p and q swaps the
        # disjuncts and the conjuncts of each.
        direction = ("(fun _h => Or.elim _h (fun _pair => Or.inr (And.intro (And.right _pair) (And.left _pair)))"
                     " (fun _pair => Or.inl (And.intro (And.right _pair) (And.left _pair))))")
        return "(Iff.intro %s %s)" % (direction, direction)
    raise ReconstructionError("commutativity over a non-commutative operator at node %d" % node)


def _iff_constant(graph, terms, node):
    premise, conclusion = graph.arguments(node)
    rule = graph.decl(node).name
    left, right = _equivalence(graph, conclusion, rule)
    fact = graph.conclusion(premise)
    if graph.kind(node) == z3.Z3_OP_PR_IFF_TRUE:
        valid = terms[left] == terms[fact] and graph.kind(right) == z3.Z3_OP_TRUE
        term = "(Iff.intro (fun _ => True.intro) (fun _ => _step_%d))" % premise
    else:
        valid = (graph.kind(fact) == z3.Z3_OP_NOT
                 and terms[left] == terms[graph.arguments(fact)[0]]
                 and graph.kind(right) == z3.Z3_OP_FALSE)
        term = "(Iff.intro _step_%d (fun _false => False.elim _false))" % premise
    if not valid:
        raise ReconstructionError("incorrect %s premise or conclusion at node %d" % (rule, node))
    return term


def _transitivity_star(graph, terms, node):
    left, right = _equivalence(graph, graph.conclusion(node), "trans*")
    edges = {}
    for premise in graph.arguments(node)[:-1]:
        first, second = _equivalence(graph, graph.conclusion(premise), "trans*")
        first, second = terms[first], terms[second]
        edges.setdefault(first, []).append((second, premise, False))
        edges.setdefault(second, []).append((first, premise, True))
    start, target = terms[left], terms[right]
    parents, pending = {start: None}, deque([start])
    while pending and target not in parents:
        current = pending.popleft()
        for successor, premise, reverse in edges.get(current, ()):
            if successor not in parents:
                parents[successor] = (current, premise, reverse)
                pending.append(successor)
    if target not in parents:
        raise ReconstructionError("trans* has no equivalence path between its endpoints at node %d" % node)

    relation = _relation(graph, left)
    path = []
    current = target
    while current != start:
        current, premise, reverse = parents[current]
        term = "_step_%d" % premise
        path.append("(%s.symm %s)" % (relation, term) if reverse else term)
    if not path:
        return "(%s.refl %s)" % (relation, _side(graph, left))
    path.reverse()
    # Balance the composition to avoid deeply nested Lean terms on long paths.
    while len(path) > 1:
        path = ["(%s.trans %s %s)" % (relation, path[index], path[index + 1])
                if index + 1 < len(path) else path[index]
                for index in range(0, len(path), 2)]
    return path[0]


def _iff_congruence(left, right):
    # Lean's core iff_congr uses propext; compose the two directions instead.
    return ("(Iff.intro (fun _h => Iff.trans (Iff.symm %s) (Iff.trans _h %s))"
            " (fun _h => Iff.trans %s (Iff.trans _h (Iff.symm %s))))" % (
                left, right, left, right))


def _congruence_term(kind, arguments):
    if kind == z3.Z3_OP_NOT:
        return "(not_congr %s)" % arguments[0]
    if kind == z3.Z3_OP_AND:
        return _fold("and_congr", arguments, "(Iff.refl True)")
    if kind == z3.Z3_OP_OR:
        return _fold("or_congr", arguments, "(Iff.refl False)")
    if kind == z3.Z3_OP_IMPLIES:
        return "(imp_congr %s %s)" % tuple(arguments)
    if kind in (z3.Z3_OP_EQ, z3.Z3_OP_IFF):
        return _iff_congruence(*arguments)
    if kind == z3.Z3_OP_XOR:
        if len(arguments) == 1:
            return arguments[0]  # (xor p) renders as p
        return "(or_congr (and_congr %s (not_congr %s)) (and_congr (not_congr %s) %s))" % (
            arguments[0], arguments[1], arguments[0], arguments[1])
    if kind == z3.Z3_OP_ITE:
        return "(or_congr (and_congr %s %s) (and_congr (not_congr %s) %s))" % (
            arguments[0], arguments[1], arguments[0], arguments[2])
    if kind == z3.Z3_OP_DISTINCT:
        pairs = ["(not_congr %s)" % _iff_congruence(left, right)
                 for index, left in enumerate(arguments) for right in arguments[index + 1:]]
        return _fold("and_congr", pairs, "(Iff.refl True)")
    raise ReconstructionError("unsupported Boolean congruence")


def _term_equality_congruence(left, right):
    """(a = b) <-> (a' = b') from a = a' and b = b', over the carrier.

    Composed from Eq.trans like _iff_congruence rather than through congr,
    whose conclusion has a metavariable head that Lean would unify with the
    formula definition's last argument instead of unfolding it.
    """
    return ("(Iff.intro (fun _h => Eq.trans (Eq.symm %s) (Eq.trans _h %s))"
            " (fun _h => Eq.trans %s (Eq.trans _h (Eq.symm %s))))" % (left, right, left, right))


def _list_congruence(arguments):
    """[a1, ..., an] = [a1', ..., an'] from one equality per element."""
    result = "(Eq.refl [])"
    for argument in reversed(arguments):
        result = "(congr (congrArg List.cons %s) %s)" % (argument, result)
    return result


def _monotonicity(graph, terms, node, atom_indices, variable_indices):
    """Congruence: equal arguments give equal applications, Boolean or over the carrier.

    Boolean connectives compose their Lean congruence lemmas; applications of
    functions and predicates go through the equality of their argument lists,
    equality and distinct over terms through congruence of Eq, and an ite term
    through ite_congr_classical. A Boolean argument of an application is
    injected by _m.bool, so its equivalence becomes an equality by propext.
    Congruence through an arithmetic operator or comparison (the legacy core
    normalizes Real atoms inside their assertions) is a grind lemma taking the
    argument equalities as premises. Returns the Lean term, whether
    ite_congr_classical is used, and the lines of any lemma to emit.
    """
    left, right = _equivalence(graph, graph.conclusion(node), "monotonicity")
    left_args, right_args = graph.arguments(left), graph.arguments(right)
    if (graph.nodes[left].declaration != graph.nodes[right].declaration
            or len(left_args) != len(right_args)):
        raise ReconstructionError("monotonicity requires matching heads and arities at node %d" % node)
    evidence = {}
    for premise in graph.arguments(node)[:-1]:
        first, second = _equivalence(graph, graph.conclusion(premise), "monotonicity")
        evidence.setdefault((terms[first], terms[second]), premise)
    arguments = []
    for first, second in zip(left_args, right_args):
        relation = _relation(graph, first)
        if terms[first] == terms[second]:
            arguments.append("(%s.refl %s)" % (relation, _side(graph, first)))
        elif (terms[first], terms[second]) in evidence:
            arguments.append("_step_%d" % evidence[terms[first], terms[second]])
        else:
            raise ReconstructionError("monotonicity is missing an argument equivalence at node %d" % node)
    if not left_args:
        # Both sides are the same constant (identical declaration, no arguments).
        return "(%s.refl %s)" % (_relation(graph, left), _side(graph, left)), False, []
    kind = graph.kind(left)
    if kind == z3.Z3_OP_UNINTERPRETED:
        # Function or predicate application: every element of the argument
        # list is a term of a sort or an injected Boolean or numeric argument.
        elements = ["(congrArg _m.bool (propext %s))" % argument if not graph.is_term(first)
                    else "(congrArg %s %s)" % (graph.injection(first), argument) if graph.is_arith(first)
                    else argument
                    for first, argument in zip(left_args, arguments)]
        if graph.is_term(left):
            return "(congrArg (%s %d) %s)" % (graph.function_family(left),
                                              variable_indices[graph.nodes[left].declaration],
                                              _list_congruence(elements)), False, []
        return "(Iff.of_eq (congrArg (_m.preds %d) %s))" % (atom_indices[graph.nodes[left].declaration],
                                                             _list_congruence(elements)), False, []
    if graph.is_term(left):
        if kind == z3.Z3_OP_ITE:
            return "(ite_congr_classical %s %s %s)" % tuple(arguments), True, []
        if kind == z3.Z3_OP_TO_REAL:
            return "(congrArg (fun (_t : Int) => ((_t : Int) : Rat)) %s)" % arguments[0], False, []
        if kind == z3.Z3_OP_TO_INT:
            return "(congrArg (fun (_t : Rat) => Rat.floor _t) %s)" % arguments[0], False, []
        if graph.is_arith(left) and (kind in _REAL_NAMES or kind in _INT_NAMES):
            lines, term = _grind_lemma(graph, node, "monotonicity", atom_indices, variable_indices)
            return term, False, lines
        raise ReconstructionError("unsupported term congruence at node %d" % node)
    if graph.is_term(left_args[0]):
        if kind == z3.Z3_OP_EQ:
            return _term_equality_congruence(*arguments), False, []
        if kind == z3.Z3_OP_DISTINCT:
            pairs = ["(not_congr %s)" % _term_equality_congruence(first, second)
                     for index, first in enumerate(arguments) for second in arguments[index + 1:]]
            return _fold("and_congr", pairs, "(Iff.refl True)"), False, []
        if kind == z3.Z3_OP_IS_INT:
            return ("(Iff.of_eq (congrArg (fun (_t : Rat) => ((Rat.floor _t : Int) : Rat) = _t) %s))"
                    % arguments[0]), False, []
        if graph.is_arith(left_args[0]) and kind in _ARITH_PREDICATE_NAMES:
            lines, term = _grind_lemma(graph, node, "monotonicity", atom_indices, variable_indices)
            return term, False, lines
        raise ReconstructionError("unsupported atom congruence at node %d" % node)
    return _congruence_term(kind, arguments), False, []


def _and_elim(graph, terms, node, shared):
    """Return the projection and the tail (premise, operand) it starts from, if any.

    With shared, the premise is a plain proof whose tails the caller binds
    (_tail_lets); a premise taking hypotheses is projected from its start.
    """
    premise, conclusion = graph.arguments(node)
    conjunction = graph.conclusion(premise)
    if graph.kind(conjunction) != z3.Z3_OP_AND:
        raise ReconstructionError("and-elim requires a conjunction at node %d" % node)
    arguments = graph.arguments(conjunction)
    for position, argument in enumerate(arguments):
        if terms[argument] == terms[conclusion]:
            base = position // _AND_ELIM_STRIDE * _AND_ELIM_STRIDE if shared else 0
            if not base:
                return _select(position, len(arguments), "_step_%d" % premise), None
            return (_select(position - base, len(arguments) - base, "_tail_%d_%d" % (premise, base)),
                    (premise, base))
    raise ReconstructionError("and-elim conclusion is not a conjunct at node %d" % node)


def _tail_lets(premise, last):
    """Bind the conjunction premise proves from every _AND_ELIM_STRIDE-th operand on, up to operand last.

    Each tail projects from the one before, so the bindings take one `.2`
    per operand however many and-elims start from them; their types are
    inferred, the subterms of the premise's unfolded conjunction.
    """
    lines = []
    for base in range(_AND_ELIM_STRIDE, last + 1, _AND_ELIM_STRIDE):
        start = ("_step_%d" % premise if base == _AND_ELIM_STRIDE
                 else "_tail_%d_%d" % (premise, base - _AND_ELIM_STRIDE))
        lines.append("  let _tail_%d_%d := %s%s" % (premise, base, start, ".2" * _AND_ELIM_STRIDE))
    return lines


def _needed_tails(tails, nodes):
    """Return the last tail of each premise that the and-elims among nodes start from."""
    needed = {}
    for node in nodes:
        if node in tails:
            premise, base = tails[node]
            needed[premise] = max(needed.get(premise, 0), base)
    return needed


def _not_or_elim(graph, terms, node):
    premise, conclusion = graph.arguments(node)
    negation = graph.conclusion(premise)
    if (graph.kind(negation) != z3.Z3_OP_NOT
            or graph.kind(graph.arguments(negation)[0]) != z3.Z3_OP_OR):
        raise ReconstructionError("not-or-elim requires a negated disjunction at node %d" % node)
    arguments = graph.arguments(graph.arguments(negation)[0])
    for position, argument in enumerate(arguments):
        injected = _inject(position, len(arguments), "_literal")
        contradiction = "(_step_%d %s)" % (premise, injected)
        if (graph.kind(conclusion) == z3.Z3_OP_NOT
                and terms[graph.arguments(conclusion)[0]] == terms[argument]):
            return "(fun _literal => %s)" % contradiction, None
        if (graph.kind(argument) == z3.Z3_OP_NOT
                and terms[graph.arguments(argument)[0]] == terms[conclusion]):
            # Native not-or-elim may cancel a double negation.
            return ("(@Decidable.byContradiction %s _df%d (fun _literal => %s))" % (
                _formula(graph, conclusion), conclusion, contradiction)), conclusion
    raise ReconstructionError("not-or-elim conclusion does not complement a disjunct at node %d" % node)


def _reachable(graph, conclusion, *more):
    """Return the formula and term nodes reachable from a conclusion, and whether any is a theory node.

    Theory nodes are Real and uninterpreted-sort terms and predicate
    applications (which may take Boolean arguments only); a conclusion without
    them is purely propositional over the atoms. With more nodes, one walk
    from all of them (their shared subterms visited once).
    """
    reachable, pending, theory = set(), [conclusion, *more], False
    while pending:
        formula = pending.pop()
        if formula in reachable:
            continue
        reachable.add(formula)
        theory = (theory or graph.is_term(formula)
                  or (graph.kind(formula) == z3.Z3_OP_UNINTERPRETED and bool(graph.arguments(formula))))
        if _trivial_distinct(graph, formula):
            continue  # rendered as True: its argument occurs nowhere to unfold
        pending.extend(graph.arguments(formula))
    return reachable, theory


def _reachable_outside_applications(graph, formula):
    """The nodes reachable from a formula without entering the arguments of uninterpreted applications.

    Reads of arrays, extensionality witnesses, default values, and array
    terms are not entered either: they are atoms of the linear forms, or
    contain only such atoms, whatever the sorts of their indices and
    elements. Neither is the condition of an arithmetic ite: the ite is
    an atom of the linear forms tied to its branches (of its own sort) by
    gate clauses, so the atoms of its condition are not the step's (the
    rewriter turns a read of a store into a Real-indexed array of Int
    elements into an Int ite over a Real index equality).
    """
    reachable, pending = set(), [formula]
    while pending:
        node = pending.pop()
        if node in reachable:
            continue
        reachable.add(node)
        if not _trivial_distinct(graph, node) and not (graph.kind(node) == z3.Z3_OP_UNINTERPRETED
                                                       and graph.arguments(node)) \
                and graph.kind(node) not in (z3.Z3_OP_SELECT, z3.Z3_OP_ARRAY_EXT, z3.Z3_OP_ARRAY_DEFAULT) \
                and not graph.is_array(node):
            arguments = graph.arguments(node)
            if graph.kind(node) == z3.Z3_OP_ITE and graph.is_arith(node):
                arguments = arguments[1:]
            pending.extend(arguments)
    return reachable


def _trivial_distinct(graph, node):
    """A distinct of one argument, which the input may state and Z3 rewrites to true."""
    return graph.kind(node) == z3.Z3_OP_DISTINCT and len(graph.arguments(node)) == 1


def _inline(graph, node, atom_indices, variable_indices, generalized=None):
    """Render a formula or term with every definition expanded, as unfold would.

    Array terms stay folded, as unfold leaves them (see _definition_names).
    generalized maps nodes to names they were generalized to, rendered in
    their place.
    """
    if generalized and node in generalized:
        return generalized[node]

    def child(sub):
        return "(%s)" % _inline(graph, sub, atom_indices, variable_indices, generalized)
    if _folded_array(graph, node):
        return _term(graph, node)
    if graph.is_term(node):
        return _term_body(graph, node, variable_indices, child, child)
    return _formula_body(graph, node, atom_indices, child, child)


def _scaled_atoms(graph, reachable):
    """Every reachable arithmetic atom with fractions: (atom, relation, terms, constant, scale, integer, type).

    terms and constant are the atom's linear form (_atom_constraint), scale
    its common denominator (not 1), integer whether it compares Int terms,
    and type the Lean number type of its arguments.
    """
    for formula in sorted(reachable):
        kind, arguments = graph.kind(formula), graph.arguments(formula)
        if (graph.is_arith(formula) or not arguments or not graph.is_arith(arguments[0])
                or (kind not in _ARITH_PREDICATE_NAMES and kind != z3.Z3_OP_EQ)):
            continue
        relation, terms, constant = _atom_constraint(graph, formula)
        scale = _common_denominator(terms, constant)
        if scale != 1:
            yield (formula, relation, terms, constant, scale, graph.is_int(arguments[0]),
                   graph.number_type_of(arguments[0]))


def _common_denominator(terms, constant):
    scale = 1
    for value in list(terms.values()) + [constant]:
        scale = scale * value.denominator // _gcd(scale, value.denominator)
    return scale


def _scaled_form(graph, terms, constant, scale, atom_indices, variable_indices, integer, folded=False,
                 generalized=None):
    """Render scale * (terms + constant) with integer coefficients, as grind's linear module wants it.

    integer is whether the form is over Int (the sort of the atom or term it
    comes from); folded renders the atoms of the form by their definitions
    (term_N) instead of written out, and generalized is _inline's.
    """
    # The linear form's variables are Real variables and opaque ite terms,
    # and in qf_lira Int ones a Real atom reaches through to_real.
    number_type = _NUMBER_TYPES["Int" if integer else "Real"]
    parts = []
    for variable in sorted(terms):
        rendered = (_term(graph, variable) if folded
                    else _inline(graph, variable, atom_indices, variable_indices, generalized))
        if not integer and graph.is_int(variable):
            rendered = "((%s : Int) : Rat)" % rendered
        parts.append("((%d : %s)) * %s" % (terms[variable] * scale, number_type, rendered))
    parts.append("((%d : %s))" % (constant * scale, number_type))
    return " + ".join(parts)


def _ite_gate_branches(graph, reachable):
    """Every reachable arithmetic ite branch with a linear form: (ite, side, branch, terms, constant, scale).

    side 0 is the then branch, 1 the else branch; terms and constant are the
    branch's linear form (_linear_term) and scale its common denominator.
    """
    for node in sorted(reachable):
        if not graph.is_arith(node) or graph.kind(node) != z3.Z3_OP_ITE:
            continue
        for side, branch in enumerate(graph.arguments(node)[1:]):
            terms = {}
            try:
                constant = _linear_term(graph, branch, Fraction(1), terms)
            except ReconstructionError:
                # A branch without a linear form, such as the dead branch
                # dividing by zero in the rewriter's factor cancellation
                # (see _validate_graph): no helper, grind splits unaided.
                continue
            yield node, side, branch, terms, constant, _common_denominator(terms, constant)


def _folded_ite_gates(graph, reachable):
    """State the branch equalities of the reachable ites and the scaled atoms over their definitions, folded.

    grind splits on an ite term by itself, but when the selected branch is a
    fractional numeral or a term with fractional coefficients it does not
    combine the resulting equality with its linear facts, and neither does
    it combine equalities whose constants are fractions, while it handles
    the same facts once scaled to integers. So each gate gives one branch
    equality under the condition or its negation, scaled to integer
    coefficients, and each fractional atom implies its scaled form.

    Returns the have lines, their names, and the nodes they are about (the
    ites and the atoms). _grind_lemma states and reverts them before it
    unfolds the definitions, so the one unfold rewrites them into the very
    terms of the goal. Written out, as they were before, the statements
    repeat every nested ite in full
    (QF_UFLIA hard16: 644 theory lemmas with 11 KB of gate text each, 7 MB
    together; a Real modular chain of six fractional steps: 5.6 MB of
    scaled gates and scaling facts in 5.9 MB), and Lean keeps every
    elaborated command's info tree to the end of the file, which then
    exceeded the 8 GB memory limit. A scaled gate or a scaling fact is
    proved with only the definitions between it and the atoms of its linear
    form unfolded (_linear_unfold), so grind sees the atoms folded, the
    nested ites among them unsplit. With arrays, whose terms the unfold
    leaves folded (_definition_names), _grind_lemma makes the nodes the
    facts are about roots of its unfold, so an ite that occurs in the goal
    only inside an array term (a stored value) is unfolded in its gates as
    in the array facts (_array_helpers) that mention it.
    """
    lines, names, nodes = [], [], set()
    for node, side, branch, terms, constant, scale in _ite_gate_branches(graph, reachable):
        condition = _formula(graph, graph.arguments(node)[0])
        hypothesis, lemma = (condition, "ite_eq_left") if side == 0 else ("(Not %s)" % condition, "ite_eq_right")
        name = "_g%d_%d" % (node, side)
        if scale == 1:
            lines.append("have %s : %s -> %s = %s := fun _h => %s _h" % (
                name, hypothesis, _term(graph, node), _term(graph, branch), lemma))
        else:
            lines.append("have %s : %s -> ((%d : %s)) * %s = (%s) := fun _h => by rw [show %s = %s from %s _h]; %sgrind"
                         % (name, hypothesis, scale, graph.number_type_of(node), _term(graph, node),
                            _scaled_form(graph, terms, constant, scale, None, None, graph.is_int(node), folded=True),
                            _term(graph, node), _term(graph, branch), lemma, _linear_unfold(graph, branch)))
        names.append(name)
        nodes.add(node)
    for formula, relation, terms, constant, scale, integer, number_type in _scaled_atoms(graph, reachable):
        name = "_s%d" % formula
        lines.append("have %s : %s -> (%s %s ((0 : %s))) := by %sgrind" % (
            name, _formula(graph, formula),
            _scaled_form(graph, terms, constant, scale, None, None, integer, folded=True), relation, number_type,
            _linear_unfold(graph, formula)))
        names.append(name)
        nodes.add(formula)
    return lines, names, nodes


def _linear_unfold(graph, node):
    """The unfold of the definitions from a term or an atom down to the atoms of its linear forms, or nothing.

    Atoms whose coefficients cancel ((+ 5 t) = (+ -7/2 t) over an ite t)
    stay folded too: the linear forms of node's sides are taken without
    dropping zero coefficients.
    """
    atoms = {}
    for side in [node] if graph.is_term(node) else graph.arguments(node):
        _linear_term(graph, side, Fraction(1), atoms)
    names = _definition_names(graph, _reachable_outside(graph, node, set(atoms)))
    return "unfold %s; " % " ".join(names) if names else ""


def _gcd(left, right):
    while right:
        left, right = right, left % right
    return left


def _grind_lemma(graph, node, prefix, atom_indices, variable_indices, opaque_tactic=None, structural=None):
    """Prove a conclusion over theory atoms with grind after unfolding its definitions.

    With structural (tactic lines), the caller's own proof attempt over the
    folded goal comes first (see _cnf_lemma and _farkas_combination); the
    attempts below unfold the definitions.

    grind decides linear arithmetic over ordered fields, congruence closure
    over uninterpreted functions, and propositional structure; the Lean kernel
    checks the proof it produces. Lean core's Rat library already depends on
    the standard axioms, so arithmetic lemmas do too. A step with premises
    (the legacy core's th-lemma and arithmetic monotonicity) is stated as the
    implication from the premise conclusions and applied to their steps.

    With opaque_tactic (Int theory lemmas, see _opaque_tactic; theory
    rewrites, see _opaque_rewrite_tactic), the atoms of the linear forms
    (div, mod, abs, ite, and applications, see _linear_term) are first
    generalized to fresh numbers, after the mod bounds (_mod_bound_facts)
    and the equalities between atoms of one key (_atom_bridge_facts) are
    stated and reverted, and that tactic is tried on the resulting linear
    goal, so neither the Euclidean operators are unfolded nor the ite atoms
    split (a lemma over a dozen div, mod, and abs atoms by negative
    numerals, and a rewrite over a dozen abs terms, used to exhaust their
    heartbeats). A lemma that needs the atoms' definitions fails that
    attempt and is proved as before, definitions unfolded.

    A farkas or bound step with coefficients gets no mod bounds: its
    combination was re-derived over the atoms alone (_check_th_lemma), so
    the generalized goal holds without them, and omega, which is complete
    for linear integer arithmetic but eliminates bounded variables by case
    analysis, took 27 s (idle machine; over two minutes under load) on a
    33-literal Farkas lemma over 26 atoms with the 28 redundant bounds in
    its context and about two seconds without them (see _combination_certified).
    """
    conclusion = graph.conclusion(node)
    premises = graph.arguments(node)[:-1]
    conclusions = [graph.conclusion(premise) for premise in premises] + [conclusion]
    reachable = set()
    for formula in conclusions:
        reachable |= _reachable(graph, formula)[0]
    statement = " -> ".join(_formula(graph, formula) for formula in conclusions)
    # An euf lemma is a congruence-closure conflict. Z3's egraph takes an ite
    # term as a leaf without arguments (euf::solver::internalize; the ite's
    # gates are tseitin clauses of their own) and applies no array axiom (the
    # array solver's are array lemmas), so such a lemma gets no ite gates and
    # no array axiom instances, and it is proved with its ite terms folded,
    # by grind alone. Over z3test's QF_AUFLIA dlx-regfile, 803 euf lemmas carried
    # about 130 folded gates each, 15 of the file's 44 MB, and their read
    # facts another 7 MB; unfolded, grind split their ites, and omega, tried
    # first over Int, exhausted the heartbeats on several of them (first does
    # not catch that). (_opaque_tactic gives an euf lemma no opaque-atom
    # attempt either: generalizing applications would hide the congruences.)
    # Its facts are those of the nodes outside the ites, as an array lemma's
    # are (below): the _t body of a store only a folded ite reaches cannot
    # meet the goal. dlx-regfile's euf lemmas stated 8,139 _t facts (1.75 MB),
    # 1,122 now (0.72 MB); its theory lemmas without the cnf one took 27 s
    # and 2.2 GB of Lean, 19 s and 1.6 GB now.
    congruence = prefix == "th_lemma" and graph.decl(node).parameters[:1] == ("euf",)
    # An array lemma is one instance of an array axiom, built over the terms
    # of its literals (array::solver::assert_select_store_axiom reads the
    # store it is given, never an ite whose branch the egraph equated with
    # it), and the array solver internalizes no ite. So it gets no ite gates
    # either and keeps its ite terms folded; its facts are those of the
    # nodes outside the ites (facts about a term only an ite reaches cannot
    # meet the folded goal), without the rewriter's reads through ites of
    # arrays (_array_helpers ite_leaves). Its tactic is unchanged. Over
    # z3test's dlx-regfile, 50 array lemmas carried about 128 gates and 37
    # read facts each and unfolded about 60 ites; the file's theory lemmas
    # without its cnf lemma took 208 s and 4.9 GB of Lean, 25 s and 2.2 GB folded.
    # The one ite such a lemma looks into is its own: the select-map axiom
    # over a map of ite equates the read with the ite of the reads
    # (_map_read_values), which is unfolded to meet the map's Lean ite.
    instance = prefix == "th_lemma" and graph.decl(node).parameters[:1] == ("array",)
    ites = ({term for term in reachable if graph.is_term(term) and graph.kind(term) == z3.Z3_OP_ITE}
            if congruence or instance else set())
    if instance:
        ites -= _map_read_values(graph, conclusion)
    scope = reachable
    if ites:
        scope = set()
        for formula in conclusions:
            scope |= _reachable_outside(graph, formula, ites)
    atoms = _opaque_int_atoms(graph, conclusions) if opaque_tactic else []
    budget = _LATTICE_LEMMA_HEARTBEATS if atoms and _lattice_step(graph, node) else 1000000
    # A rewrite or cnf lemma over sets: the sets Z3's rewriter compares
    # member by member, as auxiliary theorems before this one and facts.
    compares_arrays = (prefix == "rewrite" or graph.decl(node).parameters[:1] == ("cnf",)) and graph.arrays
    pointwise, pointwise_facts = (_pointwise_map_facts(
        graph, reachable, "%s_%d" % (prefix, node), atom_indices, variable_indices,
        members_read=prefix != "rewrite") if compares_arrays else ([], []))
    lines = pointwise + [
        "",
        "set_option maxHeartbeats %d in" % budget,
        "private theorem %s_%d (_atoms : Nat -> Prop)%s" % (prefix, node, _valuation_binder(graph)),
        "    : %s := by" % statement,
    ]
    alternatives = [] if structural is None else [structural]
    if atoms:
        # Outside the atoms first; the fallback unfolds the atoms and
        # everything under them (a child shared with the outside occurs
        # again once its atom is unfolded; unfold rejects a missing name).
        outside, inside = set(), set()
        for formula in conclusions:
            outside |= _reachable_outside(graph, formula, atoms)
        for atom in atoms:
            inside |= _reachable(graph, atom)[0]
        lines.append("  unfold " + " ".join(_definition_names(graph, outside)))
        facts, names = ([], []) if _combination_certified(graph, node) else _mod_bound_facts(graph, atoms)
        bridges, bridge_names = _atom_bridge_facts(graph, atoms)
        facts, names = facts + bridges, names + bridge_names
        if names:
            facts.append("revert " + " ".join(names))
        # A distinct of Booleans over the atoms is stated over their names.
        opaque_facts, opaque_names = _boolean_distinct_facts(
            graph, outside, atom_indices, variable_indices,
            {atom: "_o%d" % position for position, atom in enumerate(atoms)})
        alternatives.append(
            facts
            + ["generalize %s = _o%d" % (_term(graph, atom), position) for position, atom in enumerate(atoms)]
            + opaque_facts + [_without_boolean_distincts(opaque_names, opaque_tactic)])
        remaining = inside
    else:
        remaining = reachable
    gates, gate_names, gate_nodes = (_folded_ite_gates(graph, reachable)
                                     if graph.arithmetic and not (congruence or instance) else ([], [], set()))
    # Without arrays the excluded-middle facts of Boolean arguments, the
    # enumeration cases of applications, and the cast facts are stated
    # folded too (_folded_boolean_arguments, _folded_enumeration_cases,
    # _cast_facts), and reverted with the gates. With arrays the array facts
    # that mention a definition the unfold rewrites are (_array_helpers).
    fold = not graph.arrays
    if fold and graph.uninterpreted:
        lines_b, names_b, nodes_b = _folded_boolean_arguments(graph, scope)
        gates, gate_names, gate_nodes = gates + lines_b, gate_names + names_b, gate_nodes | nodes_b
    if fold and graph.enumerations:
        lines_e, names_e, nodes_e = _folded_enumeration_cases(graph, scope, variable_indices)
        gates, gate_names, gate_nodes = gates + lines_e, gate_names + names_e, gate_nodes | nodes_e
    abs_facts, abs_values = _abs_value_facts(graph, scope, atom_indices, variable_indices)
    lines_c, names_c, nodes_c, cast_facts = _cast_facts(graph, scope, atom_indices, variable_indices, node,
                                                        folded=fold, values=(abs_facts, abs_values))
    gates, gate_names, gate_nodes = gates + lines_c, gate_names + names_c, gate_nodes | nodes_c
    if cast_facts:
        abs_facts = []  # stated among the cast facts, before the floors' values
    shared = (gates, gate_names, gate_nodes, remaining)

    def bodies_through(undecided):
        """The proof bodies over the unfolded definitions, and the stores of undecided the array facts went through.

        The facts of a read go through at most undecided stores that Z3's
        rewriter does not skip into the maps below them (_array_helpers).
        """
        gates, gate_names, gate_nodes, remaining = shared
        gates = list(gates)
        if graph.arrays:
            lines_a, names_a, nodes_a, array_facts, taken = _array_helpers(
                graph, scope, atom_indices, variable_indices, congruence, ite_leaves=instance, undecided=undecided)
            gates, gate_names, gate_nodes = gates + lines_a, gate_names + names_a, gate_nodes | nodes_a
        else:
            array_facts, taken = [], 0
        if gates:
            # Stated folded and reverted, so the unfold below rewrites them as it
            # rewrites the goal; the definitions they mention outside the atoms
            # were unfolded in the goal already and are unfolded again here.
            # With arrays the unfold does not enter array terms
            # (_definition_names), and a node the facts mention may occur in the
            # goal only inside one (an index or a stored value): the mentioned
            # nodes are roots of the unfold too.
            gates.append("revert " + " ".join(gate_names))
            remaining = remaining | _reachable(graph, *sorted(gate_nodes))[0]
        roots = list(atoms) + sorted(gate_nodes)
        unfold = full_unfold = ["unfold " + " ".join(_definition_names(graph, remaining, roots))] if remaining else []
        fallback = []
        if gates:
            fallback.append("intro " + " ".join(gate_names))
        distinct_facts, distinct_names = _boolean_distinct_facts(graph, scope, atom_indices, variable_indices)
        fallback.extend(distinct_facts)
        fallback.extend(helper.strip() for helper in _theory_helpers(graph, scope, atom_indices, variable_indices,
                                                                      folded_arguments=fold, array_facts=array_facts))
        if compares_arrays:
            fallback.extend(helper.strip() for helper in _constant_array_comparisons(
                graph, reachable, atom_indices, variable_indices))
            fallback.extend(pointwise_facts)
        fallback.extend(abs_facts)
        fallback.extend(cast_facts)
        # grind alone for an euf lemma: congruence closure is its business, not
        # omega's.
        tactic = _without_boolean_distincts(distinct_names,
                                            _CONGRUENCE_TACTIC if congruence else _theory_tactic(graph))
        if cast_facts:
            # The push_cast that ends the cast facts closes a goal it
            # normalizes to an identity, (= (to_int 2.5) 2) with the floor
            # replaced by its value (_floor_shift_facts): the tactic is for
            # the goal that is left, if any.
            tactic = "all_goals (%s)" % tactic
        fallback.append(tactic)
        if ites:
            # The ites stay folded, as leaves of the congruence or of the axiom
            # instance: only the definitions outside them are unfolded, in the
            # goal and in the reverted facts (those that mention an ite keep it
            # folded, as the goal does). There is no unfolded fallback: with
            # the unfolded proof as a fallback under first, an euf lemma's text
            # doubled (register_file_instance(8): 0.71 MB of euf lemmas against
            # 1.55 MB), the fallback was never taken in the test suite, and a
            # folded attempt that spent the heartbeats before failing would
            # have left the fallback none (maxHeartbeats is per declaration).
            outside, folded_roots = set(), sorted(gate_nodes - ites)
            for formula in conclusions + folded_roots:
                outside |= _reachable_outside(graph, formula, ites)
            names = _definition_names(graph, outside, folded_roots)
            unfold = ["unfold " + " ".join(names)] if names else []
        # The store-identity alternative below keeps the full unfold: its simp
        # (_ARRAY_REWRITE_TACTIC, ite_self, _const_store_self) cannot rewrite
        # inside a folded ite definition. Its facts are still those of the scope:
        # in an euf or array lemma over ites, a store only an ite reaches gets no
        # _t fact here either, though the full unfold exposes it. No such lemma
        # takes this alternative in the test tables or generators (1,018 euf
        # lemmas over ites, none with an alternative); should one need it, Lean
        # rejects the step (completeness, not soundness), and the _t facts of
        # this alternative should then be computed over reachable.
        store_body = gates + full_unfold + fallback
        fallback = gates + unfold + fallback
        bodies = [fallback]
        if (any(graph.kind(term) == z3.Z3_OP_STORE for term in reachable) if prefix == "rewrite"
                else _store_identity_instance(graph, reachable)):
            # Z3's rewriter may have applied the store identities: the folded
            # array terms rewritten into their stores (the _t facts of
            # _array_helpers) and normalized by them first; simp may close the
            # goal. Not only rewrite steps: a th-lemma cnf over a predicate of an
            # array, p(c) \/ not p(store c n (select c n)), needs them too. The
            # alternative is tried only after the others fail; it repeats the
            # fallback's facts, so other steps get it only when one of their
            # stores is an instance of an identity.
            names = [line.split()[1] for line in store_body if line.startswith("have _t")]
            if any(decl.kind == z3.Z3_OP_CONST_ARRAY for decl in graph.declarations):
                # Reads of constant arrays evaluated, ites of a term with itself
                # dropped, stores of a constant array's own value into it
                # folded (_const_store_self), and a constant array compared
                # with one store into it decided by the stored value.
                names += ["_select_const", "ite_self", "← _const_store_self", "_const_eq_store", "_store_eq_const"]
            # Numeral expressions evaluated first, as the rewriter compares
            # indices and values by value ((/ 2 2) is 1.0).
            values, value_names = _numeral_facts(graph, reachable, atom_indices, variable_indices)
            # The final tactic for the goals simp leaves; with cast facts it
            # is under all_goals already.
            final = store_body[-1] if cast_facts else "all_goals " + store_body[-1]
            bodies.append(store_body[:-1] + values
                          + [_ARRAY_REWRITE_TACTIC % "".join(name + ", " for name in value_names + names), final])
        return bodies, taken

    # The facts of reads through stores the rewriter does not skip, into
    # the maps below them, are stated in attempts of their own, after the
    # others: a step that needs none is proved as it was without them. Each
    # such store is a case split on its index for grind, and an attempt
    # that cannot close the goal with them may not fail but run out of the
    # heartbeats (which first does not catch): a rewrite of seven reads of
    # (store (complement (store (complement (store (complement s) j0
    # false)) j1 false)) j2 false), proved in 0.5 s by the pointwise
    # facts, ran out with these facts in the attempt made without the
    # pointwise ones. The last attempts state every fact.
    deep, taken = bodies_through(_MAP_STORE_LEVELS)
    bodies = bodies_through(0)[0] if taken else deep
    if pointwise_facts:
        # Without the pointwise facts first: a step that needs none is
        # proved as it was before them, whatever they cost. grind closes
        # the classes of the sets they equate under every map and read in
        # its context, and that is not cheap: a cnf lemma over sixteen
        # nested maps of xor, proved in 0.6 s without its eleven such
        # equalities, ran out of the heartbeats with them (which first does
        # not catch). A step that needs them fails these attempts (`grind`
        # failed) and repeats its facts with them.
        stated = set(pointwise_facts)
        alternatives.extend([tactic for tactic in body if tactic not in stated] for body in bodies)
    alternatives.extend(bodies)
    if taken:
        alternatives.extend(deep)
    if len(alternatives) == 1:
        lines.extend("  " + tactic for tactic in alternatives[0])
    else:
        lines.append("  first")
        lines.extend("    | (" + "\n       ".join(alternative) + ")" for alternative in alternatives)
    return lines, "(%s_%d _atoms%s%s)" % (prefix, node, graph.valuation,
                                          "".join(" _step_%d" % premise for premise in premises))


def _map_read_values(graph, conclusion):
    """The terms a clause's literals equate with a read or the default value of a map or set operator.

    In an array lemma these are the select-map axiom's application of the
    mapped function to the reads of the arguments ((select ((_ map ite) a
    b c) i) and (ite (select a i) (select b i) (select c i))), and the
    default-map axiom's to their default values.
    """
    values = set()
    for literal in graph.clause(conclusion):
        atom = graph.arguments(literal)[0] if graph.kind(literal) == z3.Z3_OP_NOT else literal
        if graph.kind(atom) != z3.Z3_OP_EQ:
            continue
        sides = graph.arguments(atom)
        for read, value in ((sides[0], sides[1]), (sides[1], sides[0])):
            if (graph.kind(read) in (z3.Z3_OP_SELECT, z3.Z3_OP_ARRAY_DEFAULT)
                    and _set_function(graph, graph.arguments(read)[0]) is not None):
                values.add(value)
    return values


def _boolean_distinct(graph, node):
    """Whether node is a distinct of three or more Boolean arguments, which is false."""
    arguments = graph.arguments(node)
    return graph.kind(node) == z3.Z3_OP_DISTINCT and len(arguments) >= 3 and not graph.is_term(arguments[0])


# Two of any three Booleans agree, so a distinct of three or more is false;
# stated once per certificate that has one (_boolean_distinct_facts).
_BOOLEAN_DISTINCT_LEMMA = """
private theorem _bool_distinct3 {a b c : Prop} (_ab : Not (Iff a b)) (_ac : Not (Iff a c))
    (_bc : Not (Iff b c)) : False := by
  by_cases _a : a <;> by_cases _b : b <;> simp_all
""".strip("\n").split("\n")


def _without_boolean_distincts(names, tactic):
    """Run tactic after rewriting the distincts _boolean_distinct_facts named to False."""
    if not names:
        return tactic
    # Pre-order, so a distinct among another's arguments goes with the outer
    # one; simp may close the goal, so the tactic follows by <;>.
    return "(try (set_option linter.unusedSimpArgs false in simp only [%s])) <;> (%s)" % (
        ", ".join("↓ " + name for name in names), tactic)


def _boolean_distinct_facts(graph, reachable, atom_indices, variable_indices, generalized=None):
    """State every reachable distinct of three or more Booleans false, over its unfolded pairs.

    Z3's rewriter folds such a distinct to false (bool_rewriter), and a
    rewrite, theory lemma, or cnf clause over one rests on that; the
    distinct is the conjunction of its pairs' negated equivalences, quadratic
    in its arguments. Over Int, omega, tried before grind, ran out of
    heartbeats on a rewrite through distincts of 8 and 13 Booleans over Int
    atoms (z3test 3524), even with these facts as hypotheses, and first
    does not catch a heartbeat timeout. Each fact refutes the conjunction by
    its first three arguments' pairs, the first, second, and n-th conjuncts
    of _formula_body's order, through _bool_distinct3, and _grind_lemma
    rewrites the distincts to False with them before its tactic
    (_without_boolean_distincts). generalized maps the opaque atoms of
    _grind_lemma's first attempt to the names they were generalized to,
    which the facts then state in their place. Returns the tactic lines and
    the facts' names.
    """
    facts, names = [], []
    for formula in sorted(reachable):
        if not _boolean_distinct(graph, formula):
            continue
        count = len(graph.arguments(formula)) * (len(graph.arguments(formula)) - 1) // 2

        def conjunct(index):
            # The index-th of the count conjuncts of a right-nested And chain.
            return "_h" + ".2" * index + (".1" if index < count - 1 else "")
        facts.append("have _bd%d : Not %s := fun _h => _bool_distinct3 %s %s %s" % (
            formula, _inline(graph, formula, atom_indices, variable_indices, generalized),
            conjunct(0), conjunct(1), conjunct(len(graph.arguments(formula)) - 1)))
        names.append("_bd%d" % formula)
    return facts, names


# The cast lemmas a qf_lira certificate with to_real states once (_CAST_LEMMAS)
# and its theory steps instantiate per Int atom (_cast_facts), by atom kind:
# the lemma and whether the atom's arguments are swapped (s >= t is t <= s).
_CAST_ATOMS = {z3.Z3_OP_LE: ("_int_cast_le", False), z3.Z3_OP_GE: ("_int_cast_le", True),
               z3.Z3_OP_LT: ("_int_cast_lt", False), z3.Z3_OP_GT: ("_int_cast_lt", True),
               z3.Z3_OP_EQ: ("_int_cast_eq", False)}
_CAST_LEMMAS = """
private theorem _int_cast_le (s t : Int) :
    (s <= t <-> (s : Rat) <= (t : Rat)) /\\ (Not (s <= t) <-> (t : Rat) + 1 <= (s : Rat)) := by
  constructor
  . exact Rat.intCast_le_intCast.symm
  . rw [Int.not_le, Int.lt_iff_add_one_le, <- Rat.intCast_le_intCast]; push_cast; exact Iff.rfl

private theorem _int_cast_lt (s t : Int) :
    (s < t <-> (s : Rat) + 1 <= (t : Rat)) /\\ (Not (s < t) <-> (t : Rat) <= (s : Rat)) := by
  constructor
  . rw [Int.lt_iff_add_one_le, <- Rat.intCast_le_intCast]; push_cast; exact Iff.rfl
  . rw [Int.not_lt, <- Rat.intCast_le_intCast]

private theorem _int_cast_eq (s t : Int) :
    (s = t <-> (s : Rat) = (t : Rat))
      /\\ (Not (s = t) <-> (s : Rat) + 1 <= (t : Rat) \\/ (t : Rat) + 1 <= (s : Rat)) := by
  constructor
  . exact Rat.intCast_inj.symm
  . have _h : (Not (s = t) <-> s + 1 <= t \\/ t + 1 <= s) := by omega
    rw [_h, <- Rat.intCast_le_intCast, <- Rat.intCast_le_intCast]; push_cast; exact Iff.rfl
""".strip("\n").split("\n")


def _cast_facts(graph, reachable, atom_indices, variable_indices, node=None, folded=False, values=((), None)):
    """Transport the Int atoms of a theory step reaching to_real into Rat, then push the casts.

    Through (to_real t), Int terms occur in Real atoms, and a lemma such as
    x = (to_real n), (not (<= n 0)), x < 1 combines Int and Real bounds
    over the rationals after tightening each Int atom on its own
    (_polarity_constraint), but grind does not reason through Int.cast.
    So each Int atom s R t is stated equivalent, in both polarities, to its
    tightened bound between the casts of s and t (the _CAST_LEMMAS), and
    push_cast distributes every cast over sums, products, and numerals,
    leaving the casts of the Int atoms of the linear forms (variables,
    div, mod, ite) as opaque Rat terms the Real arithmetic combines.
    Conversely, a Real atom whose linear form ranges over Int terms alone
    (to_real of Int terms and numerals) is stated equivalent to an Int atom
    (_integrality_fact), so a cut that rounds it, such as
    (= (to_real n) (/ 9 4)) refuted by integrality, is an integer lemma.
    to_int is Rat.floor, and (is_int t) states t equal to the cast of its
    floor: for each floor of a Real term a the step reaches, the core
    lemmas state ((Rat.floor a : Int) : Rat) <= a < (Rat.floor a : Rat) + 1,
    the two axioms Z3's arithmetic solver adds for to_int, with which the
    floor is one more Int atom cast into Rat; the floor of an integer form
    plus a constant gets its value, and floors of terms differing by an
    integer are related (_floor_shift_facts). A lattice step (node,
    a cut or a coefficient-free farkas or bound) also gets its projection
    onto its Int atoms (_projection_facts). Steps reaching no conversion
    get nothing. values are the step's replacements of the abs terms
    that are constants by their values and the map of those terms to their
    values (_abs_value_facts): the replacements are made here, after the
    facts stated over the terms as the goal has them and before the facts
    of the floors, which are stated over the values.

    Returns the have lines stated folded, their names, the nodes they are
    about, and the remaining tactic lines. With folded, the floor bounds
    and the cast equivalences are stated over the definitions of their
    sides, folded, for _grind_lemma to revert before its unfold, as the
    ite gates (_folded_ite_gates); written out, the sides of an Int atom
    over nested ites repeat every inner ite in full (eight modular steps
    of Int under to_real: 14.7 MB of cast facts in a 15.6 MB file, which
    exceeded the 8 GB memory limit). Otherwise every fact is written out
    in the remaining lines.
    """
    if not any(graph.kind(node) in _CONVERSION_KINDS for node in reachable):
        return [], [], set(), []

    def side(argument):
        if folded:
            return _term(graph, argument)
        return "(%s)" % _inline(graph, argument, atom_indices, variable_indices)

    stated, names, nodes, facts, floors = [], [], set(), [], []
    instances = stated if folded else facts
    for formula in sorted(reachable):
        kind, arguments = graph.kind(formula), graph.arguments(formula)
        if kind in (z3.Z3_OP_TO_INT, z3.Z3_OP_IS_INT):
            if arguments[0] not in floors:
                floors.append(arguments[0])
                argument = side(arguments[0])
                instances.append("have _f%d := Rat.floor_le %s" % (arguments[0], argument))
                instances.append("have _u%d := Rat.lt_floor_add_one %s" % (arguments[0], argument))
                names.extend(["_f%d" % arguments[0], "_u%d" % arguments[0]])
                nodes.add(arguments[0])
            continue
        if kind not in _CAST_ATOMS or graph.is_term(formula) or not graph.is_arith(arguments[0]):
            continue
        if not graph.is_int(arguments[0]):
            integrality = _integrality_fact(graph, formula, atom_indices, variable_indices, folded)
            if folded and integrality:
                instances.extend(integrality[0])
                names.extend(["_r%d" % formula, "_q%d" % formula])
                nodes.update(integrality[1])
            else:
                facts.extend(integrality or [])
            continue
        lemma, swapped = _CAST_ATOMS[kind]
        sides = [side(argument) for argument in arguments]
        if swapped:
            sides.reverse()
        instances.append("have _c%d := %s %s %s" % (formula, lemma, sides[0], sides[1]))
        names.append("_c%d" % formula)
        nodes.update(arguments)
    facts.extend(values[0])
    shifts, substitutions = _floor_shift_facts(graph, floors, atom_indices, variable_indices, values[1])
    facts.extend(shifts)
    if node is not None:
        facts.extend(_projection_facts(graph, node, atom_indices, variable_indices))
    # The floors of constants are replaced by their values after every fact
    # that may mention one is stated.
    facts.extend(substitutions)
    facts.append("push_cast at *")
    return (stated, names, nodes, facts) if folded else ([], [], set(), facts)


# The most constraints _projection_facts keeps while eliminating a Real
# atom (Fourier-Motzkin multiplies them), and the most facts it states.
_PROJECTION_LIMIT = 200
_PROJECTION_FACTS = 16


def _projection_facts(graph, node, atom_indices, variable_indices):
    """Bridge the projection of a lattice step onto its Int atoms into Int: tactic lines.

    A cut or a coefficient-free farkas or bound of a _CAST step may rest on
    the integrality of floors of Real terms, as in x = 5 against (/ x 2) =
    (to_real (to_int (/ x 2))), or x - 5/4 and 3x/2 both integral: the
    rational relaxation over the casts of the Int atoms is feasible (the
    floor at 5/2; 8b - 12a = 15 for the floors a and b), so grind's Rat
    module does not refute it, and its Int module never sees the constraint
    the Real atoms imply between the Int ones. The step's linear constraints
    (premises held, clause literals denied, and the bounds f <= a < f + 1
    of each floor f of a term a) are projected onto the Int atoms here by
    eliminating every other atom exactly (an equality by substitution, the
    rest by Fourier-Motzkin), which keeps the integer solutions: an Int
    point satisfies the projection iff the Real atoms extend it. Each
    projected constraint F R 0, scaled to integer coefficients, is stated
    through its cast lemma (_CAST_LEMMAS), F R 0 over Int iff its tightened
    bound over the casts, which after push_cast is the projection grind's
    Rat module derives; grind's Int module then refutes the Int problem
    (2f = 5, 8b - 12a = 15). The facts are theorems whatever the projection
    is, so a wrong one makes Lean fail, never accept. Other steps,
    projections whose elimination rounds would exceed _PROJECTION_LIMIT
    constraints, and constraints that never mentioned a Real atom (their
    own facts are _cast_facts') get none; premises, literals and floors
    without a linear form are left out of the projection; at most
    _PROJECTION_FACTS are stated.
    """
    decl = graph.decl(node)
    if (decl.name != "th-lemma" or len(decl.parameters) != 1 or decl.parameters[0] not in ("farkas", "bound", "cut")
            or _lemma_numeric(graph, node) != _CAST):
        return []
    # A premise, literal or floor without a linear form is left out: the
    # projection of the others is still implied by the step (and the facts
    # are theorems in any case).
    constraints = []
    for literal, holds in ([(graph.conclusion(premise), True) for premise in graph.arguments(node)[:-1]]
                           + [(literal, False) for literal in graph.clause(graph.conclusion(node))]):
        try:
            constraints.append(_polarity_constraint(graph, literal, holds))
        except ReconstructionError:
            continue
    pending, floors = [atom for _, terms, _ in constraints for atom in terms], set()
    while pending:
        atom = pending.pop()
        if graph.kind(atom) != z3.Z3_OP_TO_INT or atom in floors:
            continue
        floors.add(atom)
        terms = {}
        try:
            constant = _linear_term(graph, graph.arguments(atom)[0], Fraction(-1), terms)
        except ReconstructionError:
            continue
        terms[atom] = terms.get(atom, 0) + 1
        constraints.append(("<=", dict(terms), constant))  # f - a <= 0
        constraints.append(("<", {key: -value for key, value in terms.items() if value},
                            -constant - 1))  # a - f - 1 < 0
        pending.extend(terms)
    # (relation, terms, constant, whether a Real atom was eliminated from it)
    system = [(relation, {atom: value for atom, value in terms.items() if value}, constant,
               any(not graph.is_int(atom) for atom in terms))
              for relation, terms, constant in constraints]
    while True:
        reals = sorted({atom for _, terms, _, _ in system for atom in terms if not graph.is_int(atom)})
        if not reals:
            break
        atom = reals[0]
        users = [constraint for constraint in system if atom in constraint[1]]
        rest = [constraint for constraint in system if atom not in constraint[1]]
        pivot = next((constraint for constraint in users if constraint[0] == "="), None)
        if pivot is not None:
            pairs = [(pivot, other) for other in users if other is not pivot]
        else:
            pairs = [(lower, upper) for lower in users if lower[1][atom] < 0
                     for upper in users if upper[1][atom] > 0]
        # Checked before the round builds its rows, so that no round, the
        # first included, outgrows the limit (n lower and n upper bounds
        # make n * n rows).
        if len(rest) + len(pairs) > _PROJECTION_LIMIT:
            return []
        for first, second in pairs:
            # second - (second's coefficient / first's) * first, with a
            # nonnegative multiplier unless first is an equality.
            factor = second[1][atom] / first[1][atom]
            terms = dict(second[1])
            for key, value in first[1].items():
                terms[key] = terms.get(key, 0) - factor * value
            terms = {key: value for key, value in terms.items() if value}
            if first[0] == "=":
                relation = second[0]
            else:
                relation = "<" if "<" in (first[0], second[0]) else "<="
            rest.append((relation, terms, second[2] - factor * first[2], True))
        system = []
        for relation, terms, constant, derived in rest:
            if terms:
                system.append((relation, terms, constant, derived))
            elif not {"<=": constant <= 0, "<": constant < 0, "=": constant == 0}[relation]:
                return []  # Refuted over the rationals: grind's Rat module needs no facts.
    facts, seen = [], set()
    for relation, terms, constant, derived in system:
        if not derived:
            continue
        scale = _common_denominator(terms, constant)
        divisor = functools.reduce(_gcd, [abs(int(value * scale)) for value in terms.values()])
        key = (relation, tuple(sorted((atom, value * scale / divisor) for atom, value in terms.items())),
               constant * scale / divisor)
        if key in seen:
            continue
        seen.add(key)
        form = _scaled_form(graph, terms, constant, scale, atom_indices, variable_indices, True)
        facts.append("have _p%d_%d := %s (%s) ((0 : Int))" % (node, len(facts), _CAST_LEMMA_OF[relation], form))
        if len(facts) == _PROJECTION_FACTS:
            break
    return facts


# Floors per theory step beyond which _floor_shift_facts relates none (it relates every pair).
_FLOOR_SHIFT_LIMIT = 12


# The floor of a Rat between an Int and its successor is that Int; stated once
# per certificate with a to_int or an is_int (_floor_shift_facts).
_FLOOR_VALUE_LEMMA = """
private theorem _floor_value (a : Rat) (k : Int) (_lower : (k : Rat) <= a) (_upper : a < (k : Rat) + 1) :
    Rat.floor a = k :=
  Int.le_antisymm
    (Int.lt_add_one_iff.mp (Rat.floor_lt_iff.mpr (by push_cast; exact _upper)))
    (Rat.le_floor_iff.mpr _lower)
""".strip("\n").split("\n")


def _floor_shift_facts(graph, floors, atom_indices, variable_indices, replaced=None):
    """Relate the floors of Real terms a and b whose difference D is an integer: floor a = floor b + D.

    Returns the facts and, apart, the substitutions of the floors of
    constants by their values, tactic lines for after every fact of the
    step (_cast_facts).

    Z3's rewriter moves integer summands out of a floor, (to_int (+ x 1.0))
    to (+ (to_int x) 1) and (is_int (+ x 1.0)) to (is_int x), which the
    floor bounds alone do not show (they bound each floor within 1 of its
    argument, not to an integer offset). D is a linear form over Int terms
    (numerals, and Int atoms through to_real) with integer coefficients;
    the core lemma Rat.floor_add_intCast moves it out of the floor.

    A floored term a that is such an integer D plus a constant c, as in
    (is_int (to_real n)), (to_int 0.5), or (to_int (+ (to_real n) 2.5)),
    gets floor a = D + floor c: through the core lemma Rat.floor_intCast
    when c is an integer, else through _floor_value, D + floor c being the
    integer within 1 below a. These facts are one per floor and are not
    capped.

    Each equation is stated twice: between Int terms (_zi, _di), for the
    floors that are arguments of functions, predicates, and reads, where
    congruence needs the floor's value as an Int (grind does not conclude
    it from the equation between the casts), and cast into Rat (_z, _d) for
    the Real atoms over the floors.

    The floor of a constant (D empty) is then replaced by its value in the
    goal and in every fact, by the substitutions: grind ran out of
    heartbeats on a rewrite of (= (to_int x) (to_int (- 2.0))) into bounds
    of x with (Rat.floor (-2)) in its context, value fact or not, and
    proves it at once over -2. The floor is generalized and the variable
    substituted by the value, which leaves the goal open where a simp with
    the equation may close it.

    An abs of a constant in a floored term counts by its value
    (_abs_free_value): (to_int (abs (- 2.5))) is 2. replaced maps those
    abs terms to their rendered values, which the step has put in their
    place before these facts (_abs_value_facts), so the facts are stated
    over the values too.
    """
    forms = {}
    for argument in floors:
        terms = {}
        try:
            constant = _linear_term(graph, argument, Fraction(1), terms)
        except ReconstructionError:
            continue
        for atom in [atom for atom in terms if atom in (replaced or ())]:
            constant += terms.pop(atom) * _abs_free_value(graph, atom)
        forms[argument] = ({atom: value for atom, value in terms.items() if value}, constant)
    facts, values = [], []
    cast = "congrArg (fun (_t : Int) => ((_t : Int) : Rat))"
    for argument, (terms, constant) in sorted(forms.items()):
        if any(not graph.is_int(atom) or value.denominator != 1 for atom, value in terms.items()):
            continue
        value = _scaled_form(graph, terms, Fraction(math.floor(constant)), 1, atom_indices, variable_indices, True,
                             generalized=replaced)
        side = _inline(graph, argument, atom_indices, variable_indices, replaced)
        if not terms:
            # Under try: two floored nodes may be one Lean term, the numeral
            # 1/2 and the quotient (/ 1.0 2.0), and the first one's
            # substitution then leaves the second no occurrence.
            values.append("try (generalize Rat.floor (%s) = _fv%d at *; subst _zi%d)"
                          % (side, argument, argument))
        if constant.denominator == 1:
            facts.append("have _zi%d := (congrArg Rat.floor (show (%s) = (((%s) : Int) : Rat) by push_cast; grind))"
                         ".trans (Rat.floor_intCast _)" % (argument, side, value))
        else:
            facts.append("have _zi%d : Rat.floor (%s) = (%s) := _floor_value _ _ (by push_cast; grind) "
                         "(by push_cast; grind)" % (argument, side, value))
        facts.append("have _z%d := %s _zi%d" % (argument, cast, argument))
    if len(floors) > _FLOOR_SHIFT_LIMIT:
        return facts, values
    for first, second in itertools.combinations(sorted(forms), 2):
        (first_terms, first_constant), (second_terms, second_constant) = forms[first], forms[second]
        difference = {atom: first_terms.get(atom, 0) - second_terms.get(atom, 0)
                      for atom in set(first_terms) | set(second_terms)}
        difference = {atom: value for atom, value in difference.items() if value}
        constant = first_constant - second_constant
        if (any(not graph.is_int(atom) or value.denominator != 1 for atom, value in difference.items())
                or constant.denominator != 1):
            continue
        offset = _scaled_form(graph, difference, constant, 1, atom_indices, variable_indices, True,
                              generalized=replaced)
        sides = ["(%s)" % _inline(graph, argument, atom_indices, variable_indices, replaced)
                 for argument in (first, second)]
        facts.append("have _di%d_%d := (congrArg Rat.floor (show %s = %s + (((%s) : Int) : Rat) by push_cast; grind))"
                     ".trans Rat.floor_add_intCast" % (first, second, sides[0], sides[1], offset))
        facts.append("have _d%d_%d := %s _di%d_%d" % (first, second, cast, first, second))
    return facts, values


# The conversions between the sorts of a qf_lira certificate: the injection
# of Int into Real, the floor of a Real term, and the integrality test,
# whose definition is in terms of the other two (_cast_facts).
_CONVERSION_KINDS = (z3.Z3_OP_TO_REAL, z3.Z3_OP_TO_INT, z3.Z3_OP_IS_INT)
# The core lemmas relating a relation between two Int terms to the one between their casts into Rat.
_CAST_RELATIONS = {"<=": "Rat.intCast_le_intCast", "<": "Rat.intCast_lt_intCast", "=": "Rat.intCast_inj"}
# The cast lemma (_CAST_LEMMAS) of an Int atom F R 0, by relation.
_CAST_LEMMA_OF = {"<=": "_int_cast_le", "<": "_int_cast_lt", "=": "_int_cast_eq"}


def _integrality_fact(graph, atom, atom_indices, variable_indices, folded=False):
    """State a Real atom over Int terms alone equivalent to an Int atom, or return None for any other.

    Returns the tactic lines of the facts.

    The atom is sum(terms) + constant R 0 over the Rat casts of Int terms;
    scaled by the common denominator d > 0 of its coefficients and
    constant it is F R 0 for an integer linear form F, so the atom is
    equivalent to the Int atom F R 0: grind proves the atom equivalent to
    the cast relation (Int.cast F) R 0 once push_cast has distributed the
    cast, and the core lemma relates that to F R 0. The Int atom F R 0
    is then transported back into Rat like any other (_CAST_LEMMAS), so a
    strict bound is tightened between the casts as well: with x = (to_real
    (to_int x)), (not (<= 3.0 (to_real (to_int x)))) bounds x by 2, not 3.
    An atom without a linear form (a rewrite's dead branch dividing by
    zero) gets no facts.

    With folded, the atom and the Int terms of its form are rendered by
    their definitions (see _cast_facts), and the first fact is proved
    after unfolding the atom down to those terms (_linear_unfold); the
    nodes the facts mention are returned too.
    """
    try:
        relation, terms, constant = _atom_constraint(graph, atom)
    except ReconstructionError:
        return None
    if not graph.integer_form(terms):
        return None
    scale = _common_denominator(terms, constant)
    form = _scaled_form(graph, terms, constant, scale, atom_indices, variable_indices, True, folded=folded)
    statement = _formula(graph, atom) if folded else "(%s)" % _inline(graph, atom, atom_indices, variable_indices)
    facts = ["have _r%d : %s <-> ((%s) %s ((0 : Int))) := Iff.trans (by %spush_cast; grind) %s" % (
                 atom, statement, form, relation, _linear_unfold(graph, atom) if folded else "",
                 _CAST_RELATIONS[relation]),
             "have _q%d := %s (%s) ((0 : Int))" % (atom, _CAST_LEMMA_OF[relation], form)]
    return (facts, {atom} | set(terms)) if folded else facts


def _folded_array(graph, node):
    """Whether node is an array term that lemmas keep folded (_definition_names, _inline).

    Reads, extensionality witnesses, and default values are not, even when
    their values are arrays (a row of nested arrays, an index that is an
    array, the default row of a constant array of rows): grind must see them
    as reads, witnesses, and default values of the arrays, which stay folded
    (the atoms _reachable stops at).
    """
    return graph.is_array(node) and graph.kind(node) not in (z3.Z3_OP_SELECT, z3.Z3_OP_ARRAY_EXT,
                                                             z3.Z3_OP_ARRAY_DEFAULT)


def _definition_names(graph, nodes, roots=None):
    """The definitions of nodes in unfolding order: parents before children (ids are topological).

    Array terms are left folded: written out, a chain of stores sharing
    subterms (z3test's swap and storecomm benchmarks) grows exponentially,
    and grind needs only the one-step facts _array_helpers states about them.
    Reads and extensionality witnesses are unfolded even when their values
    are arrays (_folded_array). roots, when given, are nodes of the goal
    the walk starts from besides those no other node has as an argument:
    an atom of the goal that is also stored in an array (the value of a
    folded store) is otherwise never reached.
    """
    if graph.arrays:
        # Only the nodes unfold reaches from the roots of nodes (those no
        # other one has as an argument) without entering an array term. The
        # walk stays inside nodes, which some callers cut below given atoms
        # (_reachable_outside).
        children = {child for node in nodes for child in graph.arguments(node)}
        pending, visible = [node for node in nodes if node not in children] + list(roots or ()), set()
        while pending:
            node = pending.pop()
            if node in nodes and node not in visible and not _folded_array(graph, node):
                visible.add(node)
                pending.extend(graph.arguments(node))
        nodes = visible
    return ["%s_%d" % ("term" if graph.is_term(formula) else "formula", formula)
            for formula in sorted(nodes, reverse=True)]


def _theory_helpers(graph, reachable, atom_indices, variable_indices, folded_arguments=False, array_facts=()):
    """Facts _grind_lemma states after unfolding.

    The ite gates, scaling facts, and array facts that mention definitions
    it states before (_folded_ite_gates, _array_helpers); with
    folded_arguments, the excluded-middle facts of Boolean arguments and
    the enumeration cases of applications too (_folded_boolean_arguments,
    _folded_enumeration_cases). array_facts are the other array facts
    (_array_helpers), stated here.
    """
    helpers = []
    if graph.uninterpreted and not folded_arguments:
        helpers.extend(_boolean_argument_helpers(graph, reachable, atom_indices, variable_indices))
    if graph.arithmetic and (graph.uninterpreted or graph.floors):
        helpers.extend(_real_argument_helpers(graph, reachable, atom_indices, variable_indices))
    helpers.extend(array_facts)
    if graph.enumerations:
        helpers.extend(_enumeration_helpers(graph, reachable, atom_indices, variable_indices, folded_arguments))
    return helpers


def _numeral_value(graph, node):
    """The value of an arithmetic node that is a constant (a numeral, -2 or 1/3 too), or None."""
    if not graph.is_arith(node):
        return None
    terms = {}
    try:
        constant = _linear_term(graph, node, Fraction(1), terms)
    except ReconstructionError:
        return None
    return None if any(terms.values()) else constant


def _abs_free_value(graph, node):
    """The value of an arithmetic node that is a constant once every abs of such a node is its value, or None.

    (abs (- 2.5)) is 5/2, and so are (+ (abs (- 0.5)) 2.0) and (abs (abs
    (- 2.5))): the linear form of the node (_linear_term) with each abs
    atom replaced by the absolute value of its argument's value. Any other
    atom leaves the node without a value, a floor of a constant too (an
    abs over one keeps its ite). Values are cached in
    graph.abs_free_values.
    """
    if node not in graph.abs_free_values:
        graph.abs_free_values[node] = _evaluate_abs_free(graph, node)
    return graph.abs_free_values[node]


def _evaluate_abs_free(graph, node):
    """_abs_free_value of a node, given those of the abs atoms of its linear form."""
    if not graph.is_arith(node):
        return None
    if graph.kind(node) == z3.Z3_OP_ABS:
        value = _abs_free_value(graph, graph.arguments(node)[0])
        return None if value is None else abs(value)
    terms = {}
    try:
        constant = _linear_term(graph, node, Fraction(1), terms)
    except ReconstructionError:
        return None
    for atom, coefficient in terms.items():
        if not coefficient:
            continue
        value = _abs_free_value(graph, atom) if graph.kind(atom) == z3.Z3_OP_ABS else None
        if value is None:
            return None
        constant += coefficient * value
    return constant


def _constant_abs(graph, node):
    """Whether a node is an abs of a constant (_abs_free_value)."""
    return graph.kind(node) == z3.Z3_OP_ABS and _abs_free_value(graph, node) is not None


def _abs_value_facts(graph, reachable, atom_indices, variable_indices):
    """Replace each Real abs of a constant a step reaches by its value: tactic lines, and the abs nodes' values.

    Z3's rewriter evaluates (abs (- 2.5)) to 2.5, and the rewrite of (g
    (abs (- 2.5))) into (g 2.5), of a read at that index, of a predicate
    of it, or of its floor rests on the value. Lean's abs is the ite (if t
    >= 0 then t else -t), and grind, having split it, is left with the
    branch -(-(5/2)) in the argument, which it does not identify with the
    numeral 5/2 there: its arithmetic normalizes the atoms it compares, not
    the arguments of applications (an integer value it does reach, by
    evaluating the literals), and it does not bound a sum over a split ite
    whose branch is a fraction ((to_int (- 0.75 (abs 0.5))) had no floor).
    So each such abs is stated equal to its value (_abs_free_value), which
    grind proves on its own, and then replaced by it in the goal and in
    every fact stated so far: generalized, and the variable substituted by
    the value, as the floor of a constant is (_floor_shift_facts). After
    that the step is the one of the input with the numeral written out,
    whose arguments grind compares as it does any numeral expression's.

    In node order, an abs nested in another first; the outer one is stated
    over the inner one's value, as the goal then has it. The replacement
    is not under try: the generalize always has an occurrence to abstract,
    the one in the fact just stated, also when two abs nodes are one Lean
    term ((abs 0.5) and (abs (/ 1.0 2.0)), where the first one's
    replacement leaves the goal none for the second) or the abs occurs
    only inside a folded array term; so a failure of either tactic is an
    error of the step and not a replacement silently left out. That it
    succeeds does not show that the goal had the term as it is rendered
    here: the tests check that on inputs Lean rejects with the facts
    stated and the replacements left out. An Int abs of a constant gets
    none: the simplifier evaluates it. The second result maps each
    replaced node to its rendered value, for the facts stated after the
    replacement (_inline's generalized).
    """
    lines, values = [], {}
    for node in sorted(reachable):
        if _constant_abs(graph, node) and not graph.is_int(node):
            side = _inline(graph, node, atom_indices, variable_indices, values)
            value = _numeral("Real", _abs_free_value(graph, node))
            lines.append("have _av%d : %s = %s := by grind" % (node, side, value))
            lines.append("generalize %s = _at%d at *; subst _av%d" % (side, node, node))
            values[node] = value
    return lines, values


def _distinct_values(graph, left, right):
    """Whether two index nodes are values that differ (Z3's are_distinct): numerals, or true and false.

    A negative numeral is (- n) and a Real fraction (/ n d) in a
    certificate, which Z3's rewriter compares as the values -n and n/d. A
    Bool index is a value if it is true or false.
    """
    booleans = {z3.Z3_OP_TRUE, z3.Z3_OP_FALSE}
    if graph.kind(left) in booleans and graph.kind(right) in booleans:
        return graph.kind(left) != graph.kind(right)
    left, right = _numeral_value(graph, left), _numeral_value(graph, right)
    return left is not None and right is not None and left != right


def _map_identities(graph, node, inline):
    """The identities of a map or set operator node that Z3's euf solver or rewriter may apply.

    Maps of and and or commute (euf's congruence closure) and are
    idempotent, maps of the other commutative functions (_COMMUTATIVE_MAPS)
    commute too, a double complement cancels, a set difference is the map of
    and over the first set and the complement of the second (by rfl), a map
    of constant arrays is the constant array of the function's value, and
    a map of stores at one
    index (constant arrays count as stores of their value there) is the
    store of the map of the arrays below (array_rewriter::mk_map_core).
    These need funext, so they are theorems (_SET_DEFINITIONS) instantiated
    here; grind chains them with the _t facts.
    """
    function, arguments = _set_function(graph, node), graph.arguments(node)
    rendered = " ".join(inline(argument) for argument in arguments)
    helpers = []
    if function in _SET_IDENTITIES:
        commutes, idempotent = _SET_IDENTITIES[function]
        helpers.append("  have _mc%d := %s %s" % (node, commutes, rendered))
        if arguments[0] == arguments[1]:
            helpers.append("  have _mi%d := %s %s" % (node, idempotent, inline(arguments[0])))
    if function == "Not" and _set_function(graph, arguments[0]) == "Not":
        helpers.append("  have _mn%d := _map1_not_not %s" % (node, inline(graph.arguments(arguments[0])[0])))
    if graph.kind(node) == z3.Z3_OP_ARRAY_MAP and graph.decl(node).parameters[0] in _COMMUTATIVE_MAPS:
        # Z3's congruence closure treats a map of a commutative function as
        # commutative; the swap holds pointwise, which grind proves.
        helpers.append("  have _mc%d := _map2_comm %s (by intro _x _y; grind) %s" % (node, function, rendered))
    if graph.kind(node) == z3.Z3_OP_SET_DIFFERENCE:
        # The rewriter turns (setminus a b) into ((_ map and) a ((_ map not)
        # b)) (array_rewriter::mk_set_difference), a different Lean function;
        # the other set operators share theirs with the map they become.
        helpers.append("  have _md%d : %s = _map2 And %s (_map1 Not %s) := rfl" % (
            node, inline(node), inline(arguments[0]), inline(arguments[1])))
    kinds = [graph.kind(argument) for argument in arguments]
    if all(kind == z3.Z3_OP_CONST_ARRAY for kind in kinds):
        helpers.append("  have _mk%d : %s = @_const_array %s %s %s := rfl" % (
            (node, inline(node)) + _array_types(graph, graph.decl(node).range) + (_map_application(graph, node, [
                inline(graph.arguments(argument)[0]) for argument in arguments]),)))
    elif all(kind in (z3.Z3_OP_STORE, z3.Z3_OP_CONST_ARRAY) for kind in kinds):
        indices = {graph.arguments(argument)[1] for argument in arguments if graph.kind(argument) == z3.Z3_OP_STORE}
        if len(indices) == 1:
            index = inline(indices.pop())
            arrays, values = [], []
            for position, argument in enumerate(arguments):
                if graph.kind(argument) == z3.Z3_OP_STORE:
                    arrays.append(inline(graph.arguments(argument)[0]))
                    values.append(inline(graph.arguments(argument)[2]))
                    continue
                value = inline(graph.arguments(argument)[0])
                helpers.append("  have _mk%d_%d := _const_store_self %s %s" % (node, position, value, index))
                arrays.append(inline(argument))
                values.append(value)
            helpers.append("  have _ms%d := _map%d_store %s %s %s %s" % (
                node, len(arguments), function, " ".join(arrays), index, " ".join(values)))
    return helpers


# (subset a b): every member of a is one of b. Z3's rewriter makes (=
# (setminus a b) empty) of it, the map of and over a and the complement of b
# compared with the constant array of false (array_rewriter::mk_set_subset
# and mk_set_difference); _subset_eq is that step, by function
# extensionality. It is stated after _SET_DEFINITIONS in a certificate with
# a constant array (_Graph.subset_rewrite: _const_array is defined there, and
# without one no equality with the empty set is left, the rewriter decided
# the subset).
_SUBSET_DEFINITION = [
    "def _subset {I : Type} (a b : I -> Prop) : Prop := forall _i : I, a _i -> b _i",
]
_SUBSET_REWRITE = """
private theorem _subset_eq {I : Type} (a b : I -> Prop) :
    _subset a b = (_map2 And a (_map1 Not b) = _const_array I False) := by
  apply propext
  constructor
  . intro _h
    funext _i
    exact propext (Iff.intro (fun _p => _p.2 (_h _i _p.1)) False.elim)
  . intro _h _i _a
    exact Classical.byContradiction (fun _n => Eq.mp (congrFun _h _i) (And.intro _a _n))
""".strip().split("\n")


# The facts of one read go through at most this many stores that Z3's
# rewriter does not skip (the store's index or the read's is no value, or
# they are one value) into the maps and set operators below them
# (_read_levels), counted over all the stores and maps the facts of that read
# walk (_map_read_facts). Each such store is a case split on its index for
# grind and a fact per read, so these facts are stated only in the last
# attempts of a step (_grind_lemma), and their number per read is bounded:
# without the bound a read through stores alternating with maps got a fact
# per level, 4,512 for 24 levels read at 24 indices.
_MAP_STORE_LEVELS = 8


def _read_levels(graph, array, read, undecided=0):
    """The levels of a read of a store or constant array that get facts (_array_helpers), and where the read goes on.

    Returns the store and constant-array levels, the map or set operator
    below them whose read facts the caller states too (_map_read_facts), or
    None, and the number of stores taken from undecided.

    A read of stores over a constant array gets every level and the
    constant at the bottom: Z3's rewriter evaluates such a read ((select
    (store (const v) y w) x) is (ite (= x y) w v)) with no read term of the
    levels below in the certificate.

    Over another array the rewriter skips the stores at a value index (a
    numeral, or true or false over Bool indices) other than the read's
    ((select (store (store a 1 v) 2 w) 3) is (select a 3)) and goes on with
    the read of the level where the skip stops, a store at the read's own
    index evaluated in the same step ((select (store (store a 3 5) 2 7) 3)
    is 5), so those levels get their facts too; other reads keep the single
    fact of their own level (long store chains over plain arrays at
    symbolic indices, as in z3test's swap files, would otherwise get one
    fact per level and read). When it skips every store and reaches a map
    or set operator, it evaluates the read of that ((select (store ((_ map
    -) a) 1 2) 0) is (- (select a 0))) with no read term of the map in the
    certificate.

    With undecided (a number of stores), a read gets every store down to a
    map or set operator, and the read of that, also when the rewriter does
    not skip them, if the stores from the first it does not skip down are
    at most that many. The rewriter simplifies the map member by member
    ((setminus s s) is empty, so (select (store (setminus s s) 1 false) i)
    is false) and pulls a store out of a map ((complement (store s j true))
    is (store (complement s) j false)), also at an index that is no value,
    and the read of the result is then compared with the members of the
    sets, with no read term of the map below the stores in the certificate.
    """
    stores = []
    while graph.kind(array) == z3.Z3_OP_STORE:
        stores.append(array)
        array = graph.arguments(array)[0]
    if graph.kind(array) == z3.Z3_OP_CONST_ARRAY:
        return stores + [array], None, 0
    skipped = 0
    while skipped < len(stores) and _distinct_values(graph, graph.arguments(stores[skipped])[1], read):
        skipped += 1
    below = array if _set_function(graph, array) is not None else None
    if skipped == len(stores):
        return stores, below, 0
    if below is not None and len(stores) - skipped <= undecided:
        return stores, below, len(stores) - skipped
    # The skipped levels and the store where the skip stops.
    return stores[:skipped + 1], None, 0


def _stored_rows(graph, row):
    """The stores and constant arrays a read of a row of nested arrays may evaluate to, in order.

    They are the rows stored along the store chain of the array read (and a
    constant array's row at its bottom); when that array is a row read
    itself (three levels or more), the rows stored in the rows it may
    evaluate to.
    """
    arrays, rows = [graph.arguments(row)[0]], []
    if graph.kind(arrays[0]) == z3.Z3_OP_SELECT and graph.is_array(arrays[0]):
        arrays = _stored_rows(graph, arrays[0])
    for outer in arrays:
        while graph.kind(outer) == z3.Z3_OP_STORE:
            rows.append(graph.arguments(outer)[2])
            outer = graph.arguments(outer)[0]
        if graph.kind(outer) == z3.Z3_OP_CONST_ARRAY:
            rows.append(graph.arguments(outer)[0])
    seen = set()
    return [value for value in rows if graph.kind(value) in (z3.Z3_OP_STORE, z3.Z3_OP_CONST_ARRAY)
            and not (value in seen or seen.add(value))]


def _ite_branches(graph, array):
    """The stores and constant arrays among the branches of an ite over arrays, through nested ites, in order."""
    pending, seen, branches = [array], set(), []
    while pending:
        node = pending.pop()
        if node in seen:
            continue
        seen.add(node)
        if graph.kind(node) == z3.Z3_OP_ITE:
            pending.extend(reversed(graph.arguments(node)[1:]))
        elif graph.kind(node) in (z3.Z3_OP_STORE, z3.Z3_OP_CONST_ARRAY):
            branches.append(node)
    return branches


def _level_fact(graph, name, store, read, inline):
    """The fact of a read at read of one store or constant-array level (_read_levels)."""
    if graph.kind(store) == z3.Z3_OP_STORE:
        return "  have %s := _store_apply %s %s" % (
            name, " ".join(inline(argument) for argument in graph.arguments(store)), inline(read))
    return "  have %s := _select_const (I := %s) %s %s" % (
        name, _array_types(graph, graph.decl(store).range)[0], inline(graph.arguments(store)[0]), inline(read))


def _map_read_facts(graph, prefix, array, read, inline, undecided=0):
    """The facts of a read at read of a map or set operator array, named prefix, prefix_1, ...

    The function over the reads of its arrays (the select-map axiom), at
    every map below it too, since Z3's rewriter evaluates a read through
    nested maps ((select (map not (map or a b)) i) is (not (or (select a i)
    (select b i)))) with no read term of the levels in between, and on into
    the stores (their levels as for a read of a store, and a map those reach)
    and constant arrays below them. All of them together go through at most
    undecided stores the rewriter does not skip (_read_levels). Returns the
    facts and the number of such stores they went through.
    """
    helpers, pending, seen, taken = [], [array], set(), 0
    while pending:
        current = pending.pop(0)
        if current in seen:
            continue
        seen.add(current)
        if graph.kind(current) in (z3.Z3_OP_STORE, z3.Z3_OP_CONST_ARRAY):
            levels, below, more = _read_levels(graph, current, read, undecided - taken)
            taken += more
            for store in levels:
                helpers.append(_level_fact(graph, prefix if not helpers else "%s_%d" % (prefix, len(helpers)),
                                           store, read, inline))
            if below is not None:
                pending.append(below)
            continue
        reads = tuple("(_select %s %s)" % (inline(argument), inline(read)) for argument in graph.arguments(current))
        helpers.append("  have %s : _select %s %s = %s := rfl" % (
            prefix if not helpers else "%s_%d" % (prefix, len(helpers)), inline(current), inline(read),
            _map_application(graph, current, reads)))
        pending.extend(argument for argument in graph.arguments(current)
                       if _set_function(graph, argument) is not None
                       or graph.kind(argument) in (z3.Z3_OP_STORE, z3.Z3_OP_CONST_ARRAY))
    return helpers, taken


def _array_helpers(graph, reachable, atom_indices, variable_indices, congruence=False, ite_leaves=False,
                   undecided=0):
    """Instantiate the array facts for the reads of stores and the extensionality witnesses a lemma reaches.

    Array terms, _select, and _store stay folded, so grind compares reads by
    congruence; each store or ite over arrays is stated equal to its body;
    each read of a store gets its value as an ite over the index equality
    (_store_apply), each witness (_ array-ext 0) of two arrays the clause
    that they are equal or differ there (_array_ext). These are the array
    solver's axiom instances; grind combines them with the lemma's literals.

    The facts are stated over the definitions of the nodes they mention
    (term_N, formula_N), for _grind_lemma to revert before its unfold, as
    the ite gates (_folded_ite_gates). Written out, an index or a stored
    value repeated every nested ite and application below it in full: over
    the shared ite DAG of z3test's QF_AUFLIA dlx-regfile the facts of one
    cnf lemma did not finish rendering in five minutes. Array terms (which
    the unfold leaves folded), constants, variables, and numerals are
    written as before, and the facts of a node that mention nothing else
    are not reverted: around the many facts of z3test's storecomm files,
    whose stores are over variables, revert, unfold, and intro took Lean
    from 118 s and 5.6 GB to 155 s and 7.9 GB. Returns the facts to revert,
    their names, the nodes they mention, the facts to state after the
    unfold, and the number of stores Z3's rewriter does not skip that the
    facts of the reads went through: at most undecided per read
    (_read_levels), and with none the facts are those of undecided 0.

    With congruence (an euf lemma, see _grind_lemma), only the facts Z3's
    congruence closure may use are stated: the bodies of the folded array
    terms but ites (leaves to the egraph) and the commutativity of maps and
    of extensionality witnesses (its comm claims), not the array axioms'
    instances. With ite_leaves (an array lemma whose ites stay folded), an
    ite over arrays gets no body and a read of one no facts of its
    branches' reads (_si, the rewriter's evaluation): the array solver
    instantiates its axioms over the terms of the lemma's literals.
    """
    mentioned, current, reverted, plain = set(), set(), [], []

    def inline(sub):
        if graph.arguments(sub) and not _folded_array(graph, sub):
            current.add(sub)
            return _term(graph, sub) if graph.is_term(sub) else _formula(graph, sub)
        return "(%s)" % _inline(graph, sub, atom_indices, variable_indices)

    def read_facts(arrays, read, level, below_prefix):
        """The facts of the read at read of each of arrays (stores and constant arrays).

        The levels of each (_read_levels), named level % their position
        among the levels of all, and the read facts of the map below them
        (_map_read_facts), named from below_prefix % the array's position.
        """
        nonlocal taken
        count, left = 0, undecided
        for position, array in enumerate(arrays):
            levels, below, more = _read_levels(graph, array, read, left)
            left -= more
            for store in levels:
                helpers.append(_level_fact(graph, level % count, store, read, inline))
                count += 1
            if below is not None:
                facts, more = _map_read_facts(graph, below_prefix % position, below, read, inline, left)
                left -= more
                helpers.extend(facts)
        taken += undecided - left

    helpers, taken = [], 0
    for node in sorted(reachable):
        # The facts of one node are reverted together if any mentions a
        # definition the unfold rewrites.
        first = len(helpers)
        current.clear()
        kind = graph.kind(node)
        if graph.is_array(node) and (kind in (z3.Z3_OP_STORE, z3.Z3_OP_CONST_ARRAY)
                                     or (kind == z3.Z3_OP_ITE and not (congruence or ite_leaves))
                                     or _set_function(graph, node) is not None
                                     or (kind == z3.Z3_OP_UNINTERPRETED and graph.arguments(node))):
            # Array terms stay folded (_definition_names); each store, ite
            # over arrays, constant array, and application of a function
            # into arrays is related to its body one level down (grind's
            # congruence closure then compares applications by arguments).
            helpers.append("  have _t%d : %s = %s := rfl" % (
                node, _term(graph, node), _term_body(graph, node, variable_indices, inline, inline)))
        elif congruence:
            pass  # Congruence closure applies no array axiom (nor ite gate).
        elif kind == z3.Z3_OP_SELECT and graph.kind(graph.arguments(node)[0]) in (z3.Z3_OP_STORE,
                                                                                  z3.Z3_OP_CONST_ARRAY):
            # A read of a store: its value one level down, and the levels
            # below that the rewriter evaluates (_read_levels).
            array, read = graph.arguments(node)
            levels, below, more = _read_levels(graph, array, read, undecided)
            for level, store in enumerate(levels):
                name = "_s%d" % node if level == 0 else "_s%d_%d" % (node, level)
                helpers.append(_level_fact(graph, name, store, read, inline))
            if below is not None:
                facts, deeper = _map_read_facts(graph, "_sm%d" % node, below, read, inline, undecided - more)
                helpers.extend(facts)
                more += deeper
            taken += more
        elif kind == z3.Z3_OP_SELECT and graph.kind(graph.arguments(node)[0]) == z3.Z3_OP_ITE and not ite_leaves:
            # A read of an ite over arrays: Z3's rewriter pushes the read
            # into the branches ((select (ite c a b) i) is (ite c (select a
            # i) (select b i))) and evaluates the reads of stores and
            # constant arrays there, with no read term of the branches in
            # the certificate. Each such branch, through nested ites, gets
            # the facts of a read of it (its levels as for a read of a store).
            array, read = graph.arguments(node)
            read_facts(_ite_branches(graph, array), read, "_si%d_%%d" % node, "_sim%d_%%d" % node)
        elif (kind == z3.Z3_OP_SELECT and graph.kind(graph.arguments(node)[0]) == z3.Z3_OP_SELECT
              and graph.is_array(graph.arguments(node)[0])):
            # A read of a row of nested arrays: Z3's rewriter evaluates the
            # row read of a store at its own index to the stored row, then
            # the read of that row ((select (select (store a i (store r j
            # v)) i) j) is v) with no read term of the stored row in the
            # certificate. Each row stored along the outer store chain (or a
            # constant array's row) that is a store or a constant array gets
            # the facts of a read of it at the read's index (its levels as
            # for a read of a store); grind relates them to this read
            # through the row read's own fact.
            row, read = graph.arguments(node)
            read_facts(_stored_rows(graph, row), read, "_n%d_%%d" % node, "_nm%d_%%d" % node)
        if graph.is_array(node) and _set_function(graph, node) is not None:
            helpers.extend(_map_identities(graph, node, inline))
        if kind == z3.Z3_OP_SET_SUBSET and graph.subset_rewrite and not congruence:
            # What Z3's rewriter makes of it (_subset_eq); grind chains it
            # with the _t facts of the map and the constant array.
            helpers.append("  have _sb%d := _subset_eq %s %s" % (
                node, inline(graph.arguments(node)[0]), inline(graph.arguments(node)[1])))
        if congruence:
            if kind == z3.Z3_OP_ARRAY_EXT:
                helpers.append("  have _xc%d := _array_diff_comm %s %s %s" % (
                    node, _nonempty(graph, graph.decl(node).range), inline(graph.arguments(node)[0]),
                    inline(graph.arguments(node)[1])))
        elif kind == z3.Z3_OP_SELECT and _set_function(graph, graph.arguments(node)[0]) is not None:
            # A read of a map or set operator: the connective over the reads
            # of its arrays (the select-map axiom), at every map below it
            # too, since Z3's rewriter evaluates a read through nested maps
            # ((select (map not (map or a b)) i) is (not (or (select a i)
            # (select b i)))) with no read term of the levels in between,
            # and on into the stores and constant arrays below them.
            facts, more = _map_read_facts(graph, "_m%d" % node, graph.arguments(node)[0],
                                          graph.arguments(node)[1], inline, undecided)
            helpers.extend(facts)
            taken += more
        elif kind == z3.Z3_OP_ARRAY_EXT:
            # Z3's congruence closure takes the witness as commutative (an
            # euf hint's (comm (= (array-ext b a) (array-ext a b))) claim);
            # _array_diff_comm states it for grind.
            arguments = (_nonempty(graph, graph.decl(node).range), inline(graph.arguments(node)[0]),
                         inline(graph.arguments(node)[1]))
            helpers.append("  have _x%d := _array_ext %s %s %s" % ((node,) + arguments))
            helpers.append("  have _xc%d := _array_diff_comm %s %s %s" % ((node,) + arguments))
        elif kind == z3.Z3_OP_ARRAY_DEFAULT and graph.kind(graph.arguments(node)[0]) == z3.Z3_OP_CONST_ARRAY:
            array = graph.arguments(node)[0]
            helpers.append("  have _d%d := _default_const %s %s" % (
                node, _unbounded(graph, array, explicit=True), inline(graph.arguments(array)[0])))
        elif kind == z3.Z3_OP_ARRAY_DEFAULT and graph.kind(graph.arguments(node)[0]) == z3.Z3_OP_STORE:
            array = graph.arguments(node)[0]
            helpers.append("  have _d%d := %s" % (node, _default_store_fact(
                graph, array, " ".join(inline(argument) for argument in graph.arguments(array)))))
        elif (kind == z3.Z3_OP_ARRAY_DEFAULT and graph.generic
              and _set_function(graph, graph.arguments(node)[0]) is not None):
            helpers.append(_default_map_fact(graph, "_d%d" % node, graph.arguments(node)[0], inline))
        (reverted if current else plain).extend(helpers[first:])
        mentioned |= current
    return ([helper.strip() for helper in reverted], [helper.split()[1] for helper in reverted], mentioned,
            [helper.strip() for helper in plain], taken)


# The Boolean functions a map or set operator applies to the members of sets,
# on truth tables as bit masks (full is the table of true), by the function's
# name in a map declaration; the set operators are named as the maps Z3's
# rewriter makes of them, a difference "setminus".
_POINTWISE_FUNCTIONS = {
    "not": lambda full, a: full & ~a,
    "and": lambda full, a, b: a & b,
    "or": lambda full, a, b: a | b,
    "=>": lambda full, a, b: (full & ~a) | b,
    "xor": lambda full, a, b: a ^ b,
    "=": lambda full, a, b: full & ~(a ^ b),
    "distinct": lambda full, a, b: a ^ b,
    "ite": lambda full, c, a, b: (c & a) | (full & ~c & b),
    "setminus": lambda full, a, b: a & ~b,
}
_POINTWISE_SET_OPERATORS = {z3.Z3_OP_SET_UNION: "or", z3.Z3_OP_SET_INTERSECT: "and",
                            z3.Z3_OP_SET_DIFFERENCE: "setminus", z3.Z3_OP_SET_COMPLEMENT: "not"}
# A set term is compared pointwise (_pointwise_map_facts) over at most this
# many leaves (sets, Boolean values, and stored-index tests; its truth table
# has 2^n rows) and this many maps and stores, counted as its member formula
# writes them (the comparison writes that formula out): as a tree, and an
# argument once per occurrence in its map's formula (_pointwise_occurrences;
# a map of xor writes each argument twice and a map of ite its condition, so
# the formula of a nest of them doubles per level: sixteen nested maps of
# xor wrote 10.8 MB and Lean ran out of heartbeats while the limit was on
# the number of maps). A larger term is taken as a set of its own. A step
# that reaches more than _POINTWISE_SETS Boolean set terms gets no
# pointwise facts.
_POINTWISE_LEAVES = 8
_POINTWISE_SIZE = 48
_POINTWISE_SETS = 256


def _pointwise_function(graph, node):
    """The Boolean function a map or set operator node applies to its sets' members (_POINTWISE_FUNCTIONS), or None.

    None for any other node, and for a map of another function or over
    elements that are not Booleans (a map of <= over Int arrays is a set,
    but not a function of sets).
    """
    kind = graph.kind(node)
    if kind in _POINTWISE_SET_OPERATORS:
        return _POINTWISE_FUNCTIONS[_POINTWISE_SET_OPERATORS[kind]]
    if kind != z3.Z3_OP_ARRAY_MAP:
        return None
    decl = graph.decl(node)
    if any(_array_components(sort)[1] != "Bool" for sort in decl.domain):
        return None
    return _POINTWISE_FUNCTIONS.get(decl.parameters[0])


def _pointwise_occurrences(graph, node):
    """How many times the member formula of a map or set operator writes that of each argument (_map_application)."""
    marks = ["\0%d\0" % position for position in range(len(graph.arguments(node)))]
    written = _map_application(graph, node, marks)
    return [written.count(mark) for mark in marks]


def _expanded_table(table, leaves, onto):
    """A truth table over leaves as the table over onto, a tuple that holds every one of leaves."""
    if leaves == onto:
        return table
    positions = [onto.index(leaf) for leaf in leaves]
    expanded = 0
    for row in range(1 << len(onto)):
        source = sum(((row >> position) & 1) << bit for bit, position in enumerate(positions))
        expanded |= ((table >> source) & 1) << row
    return expanded


def _essential_table(leaves, table):
    """A truth table over the leaves it depends on alone: those leaves and the table over them.

    Two tables are of one function exactly if these agree.
    """
    rows = range(1 << len(leaves))
    positions = [position for position in range(len(leaves))
                 if any(((table >> row) ^ (table >> (row ^ (1 << position)))) & 1 for row in rows)]
    reduced = 0
    for row in range(1 << len(positions)):
        # The row of the full table with the other leaves false.
        source = sum(((row >> bit) & 1) << position for bit, position in enumerate(positions))
        reduced |= ((table >> source) & 1) << row
    return tuple(leaves[position] for position in positions), reduced


def _pointwise_map_facts(graph, reachable, name, atom_indices, variable_indices, members_read=False):
    """Facts for a step whose sets Z3's rewriter compares member by member.

    array_rewriter::mk_map_core simplifies a map of connectives over sets
    as it simplifies the connective over their members, and an equality
    between the results is decided when they are constant arrays: (setminus
    s s) is the empty set, a double complement cancels, (intersection
    (complement s) (setminus s t)) is empty, nested maps of and are
    flattened and sorted, (= ((_ map and) s (complement s)) full) is false.
    The certificate holds the sets before and after, and no fact about a
    single map relates them. So each set term over Booleans the step
    reaches is read as a Boolean function of its leaves: the sets its maps,
    set operators, and stores are over, the Boolean values it stores or
    holds in constant arrays (other than true and false), and, per stored
    index, whether the member's index is that one (a store is the stored
    value there and the set's member elsewhere, so a map of stores at one
    index is the store of the map). Its truth table is computed here; two
    terms of one function are stated equal, and the sides of an equality
    whose functions differ in every row are stated different. Both are
    proved by function extensionality from an auxiliary theorem over the
    members as propositions, which grind proves with nothing else in its
    context; the member formulas are what the sets' definitions unfold to
    at an index. Two sets of one member formula (a union and the map of or
    over the same sets) are equal by rfl at each index, without a theorem,
    and an auxiliary theorem is stated once per certificate: a later
    comparison of the same text uses it (_Graph.pointwise_theorems). The
    tables only choose the facts: Lean checks each.

    A (subset a b) the step reaches is compared the same way: the rewriter
    makes (= (setminus a b) empty) of it and simplifies that difference
    member by member, so the function of the difference chooses the facts:
    that the subset holds, that it fails (at any index, at a stored one,
    or at one off the stored ones), that it is the implication between the
    values of constant arrays, and that the difference as _subset_eq writes
    it is the set the rewriter's equality is left with (see the loop over
    subsets).

    With members_read (a cnf lemma, whose clause the solver assumed about
    members while the assertion it is tied to equates sets), each such
    equality also implies that its sides' members agree at every index the
    lemma reads from a set of its sort, by congruence, unless there are
    more than _COMPARISON_READS such facts. These facts alone are stated
    for a lemma that reaches a store of a set and no map or set operator:
    Z3 evaluates the maps of an assertion at a member under another
    assertion that equates a set with a store ((= (store s j false) t)
    makes (select t j) false), and the clause it logs has the members
    only.

    Returns the lines of the auxiliary theorems stated here, named
    name_pwN, and the facts.
    """
    def inline(sub):
        return "(%s)" % _inline(graph, sub, atom_indices, variable_indices)

    def boolean_set(node):
        return graph.is_array(node) and _array_components(graph.decl(node).range)[1] == "Bool"

    sets = [node for node in sorted(reachable) if boolean_set(node)]
    subsets = [node for node in sorted(reachable) if graph.kind(node) == z3.Z3_OP_SET_SUBSET]
    mapped = any(_pointwise_function(graph, node) is not None for node in sets)
    if len(sets) > _POINTWISE_SETS or not (mapped or subsets or (members_read and any(
            graph.kind(node) == z3.Z3_OP_STORE for node in sets))):
        return [], []
    # Per set: its leaves, its truth table over them, and the number of maps
    # and stores its member formula writes (_POINTWISE_SIZE). Ids are
    # topological, so arguments come first. A leaf is a set, a Boolean
    # value, or the proposition that the member's index is a stored one,
    # named by its kind and node.
    tables, functions = {}, set()

    def value_table(value):
        if graph.kind(value) in (z3.Z3_OP_TRUE, z3.Z3_OP_FALSE):
            return (), int(graph.kind(value) == z3.Z3_OP_TRUE), 0
        return (("value", value),), 2, 0

    for node in sets:
        kind, arguments = graph.kind(node), graph.arguments(node)
        function = _pointwise_function(graph, node)
        if kind == z3.Z3_OP_CONST_ARRAY:
            tables[node] = value_table(arguments[0])
            continue
        if kind == z3.Z3_OP_STORE and arguments[0] in tables:
            # The stored value at the stored index, the array's member elsewhere.
            function = _POINTWISE_FUNCTIONS["ite"]
            operands = [((("index", arguments[1]),), 2, 0), value_table(arguments[2]), tables[arguments[0]]]
            written = (1, 1, 1)
        elif function is not None and all(argument in tables for argument in arguments):
            operands = [tables[argument] for argument in arguments]
            written = _pointwise_occurrences(graph, node)
        else:
            operands = None
        if operands is not None:
            leaves = tuple(sorted({leaf for operand in operands for leaf in operand[0]}))
            size = 1 + sum(count * operand[2] for count, operand in zip(written, operands))
            if len(leaves) <= _POINTWISE_LEAVES and size <= _POINTWISE_SIZE:
                full = (1 << (1 << len(leaves))) - 1
                tables[node] = (leaves, function(full, *(_expanded_table(operand[1], operand[0], leaves)
                                                         for operand in operands)), size)
                functions.add(node)
                continue
        tables[node] = ((("set", node),), 2, 0)
    keys = {node: (graph.decl(node).range,) + _essential_table(*tables[node][:2]) for node in sets}

    def value_member(value, names):
        return names.get(("value", value), "True" if graph.kind(value) == z3.Z3_OP_TRUE else "False")

    def member(node, names):
        """The member formula of a set over the names of its leaves, as the set's definition unfolds at an index."""
        kind, arguments = graph.kind(node), graph.arguments(node)
        if kind == z3.Z3_OP_CONST_ARRAY:
            return value_member(arguments[0], names)
        if node not in functions:
            return names[("set", node)]
        if kind == z3.Z3_OP_STORE:
            return "(@ite Prop %s (Classical.propDecidable _) %s %s)" % (
                names[("index", arguments[1])], value_member(arguments[2], names), member(arguments[0], names))
        return _map_application(graph, node, [member(argument, names) for argument in arguments])

    theorems, facts = [], []

    def leaf_member(leaf, at):
        """What a leaf is at an index: the member of its set, its value, or whether the index is its stored one."""
        kind, node = leaf
        if kind == "set":
            return "(_select %s %s)" % (inline(node), at)
        return inline(node) if kind == "value" else "(%s = %s)" % (at, inline(node))

    def auxiliary(left, right, statement, third=None, at="_i"):
        """The auxiliary theorem of two sets applied to their leaves' members at _i, stated unless it was before.

        None if the two have one member formula (sets of one function may).
        With third, a set too, the statement is over the members of the
        three, and None if the third's member formula is the difference of
        the others' as written; with at, the theorem is applied to the
        members at that index.
        """
        nodes = (left, right) if third is None else (left, right, third)
        leaves = sorted(set().union(*(tables[node][0] for node in nodes)))
        names = {leaf: "_p%d" % position for position, leaf in enumerate(leaves)}
        sides = tuple(member(node, names) for node in nodes)
        if third is None:
            trivial = sides[0] == sides[1]
        else:
            trivial = "(And %s (Not %s))" % sides[:2] == sides[2]
        if trivial:
            return None
        stated = ["%s :" % (" (%s : Prop)" % " ".join(names[leaf] for leaf in leaves) if leaves else ""),
                  "    %s := by grind" % (statement % sides)]
        theorem = graph.pointwise_theorems.get(tuple(stated))
        if theorem is None:
            theorem = graph.pointwise_theorems[tuple(stated)] = "%s_pw%d" % (name, len(theorems) // 3)
            theorems.extend(["", "private theorem %s%s" % (theorem, stated[0]), stated[1]])
        return "(%s)" % " ".join([theorem] + [leaf_member(leaf, at) for leaf in leaves])

    # A step without a map or set operator (a cnf lemma that reaches a store)
    # gets the members of its equalities' sides alone, below.
    classes = {}
    for node in sets if mapped else ():
        classes.setdefault(keys[node], []).append(node)
    for members in classes.values():
        # The first set that is not a map or store (there is at most one: a
        # leaf or a constant array is its own function), else the first.
        first = next((node for node in members if node not in functions), members[0])
        for node in members:
            if node != first:
                proof = auxiliary(node, first, "(Iff %s %s)")
                facts.append("have _pw%d : %s = %s := funext (fun _i => %s)" % (
                    node, inline(node), inline(first), "rfl" if proof is None else "propext %s" % proof))
    equalities = [node for node in sorted(reachable) if graph.kind(node) == z3.Z3_OP_EQ
                  and all(argument in keys for argument in graph.arguments(node))
                  and any(argument in functions for argument in graph.arguments(node))]
    for node in equalities if mapped else ():
        left, right = graph.arguments(node)
        (sort, leaves, table), other = keys[left], keys[right]
        # Functions that differ in every row depend on the same leaves. The
        # sets then differ at any index, so the index sort must be inhabited:
        # over a carrier the interpretation says so only next to an
        # extensionality witness (_carrier_inhabited); without, no fact.
        index = _array_components(sort)[0]
        if other == (sort, leaves, table ^ ((1 << (1 << len(leaves))) - 1)) and _inhabited(graph, index):
            facts.append("have _pwn%d : %s = %s -> False := fun _h => Nonempty.elim %s "
                         "(fun _i => %s (Iff.of_eq (congrFun _h _i)))" % (
                             node, inline(left), inline(right), _nonempty(graph, index),
                             auxiliary(left, right, "Not (Iff %s %s)")))
    for node in subsets:
        # (subset a b) is (= (setminus a b) empty) for the rewriter, which
        # simplifies the difference member by member like any map: the
        # function of the difference chooses the fact. Empty in every row,
        # the subset holds; full in every row, it fails at any index (the
        # index sort inhabited as for _pwn); full in every row of a stored
        # index (a store pulled out of the map is compared with the empty
        # set there: (subset full (store s 1 false)) is false), it fails at
        # that index. Whenever it is neither empty nor full, the difference
        # as _subset_eq writes it (_array_helpers states that fact) equals
        # the first set of the step with its function, which the rewriter's
        # equality compares with the empty set.
        left, right = graph.arguments(node)
        sort = graph.decl(left).range
        leaves = tuple(sorted(set(tables[left][0]) | set(tables[right][0])))
        if len(leaves) > _POINTWISE_LEAVES:
            continue  # (each set is over at most that many; the two together may be over more)
        rows = range(1 << len(leaves))
        full = (1 << len(rows)) - 1
        difference = (_expanded_table(tables[left][1], tables[left][0], leaves)
                      & ~_expanded_table(tables[right][1], tables[right][0], leaves) & full)
        index = _array_components(sort)[0]
        # An inhabitant of the index sort. Over a carrier the interpretation
        # states one only next to an extensionality witness
        # (_carrier_inhabited); it always has the constants' values (elems).
        inhabited = _nonempty(graph, index) if _inhabited(graph, index) else "(Nonempty.intro (_m.elems 0))"
        if difference == 0:
            proof = auxiliary(left, right, "(%s -> %s)")
            facts.append("have _pws%d : _subset %s %s := fun _i => %s" % (
                node, inline(left), inline(right), "fun _h => _h" if proof is None else proof))
            continue
        if difference == full:
            # (grind does not prove the negated implication as one statement.)
            proof = auxiliary(left, right, "(And %s (Not %s))")
            facts.append("have _pwsn%d : _subset %s %s -> False := fun _h => Nonempty.elim %s "
                         "(fun _i => %s.2 (_h _i %s.1))" % (node, inline(left), inline(right), inhabited, proof, proof))
            continue
        positions = [position for position, leaf in enumerate(leaves) if leaf[0] == "index"]
        stored = next((position for position in positions if all(
            (difference >> row) & 1 for row in rows if (row >> position) & 1)), None)
        if stored is not None:
            proof = "(%s rfl)" % auxiliary(left, right, "(_p%d -> (And %%s (Not %%s)))" % stored,
                                           at=inline(leaves[stored][1]))
            facts.append("have _pwsn%d : _subset %s %s -> False := fun _h => %s.2 (_h %s %s.1)" % (
                node, inline(left), inline(right), proof, inline(leaves[stored][1]), proof))
        elif (positions and graph.subset_rewrite and index in _UNBOUNDED and all(
                (difference >> row) & 1 for row in rows if not any((row >> position) & 1 for position in positions))):
            # Full off the stored indices, whatever the other leaves are
            # ((subset full (store empty 0 true)), which the rewriter decides
            # by the default values): it fails at an index that is none of
            # them, which exists over Int and Real (_UNBOUNDED_THEOREMS,
            # stated next to a constant array).
            proof = "(%s %s)" % (
                auxiliary(left, right, "(%s(And %%s (Not %%s)))" % "".join(
                    "(Not _p%d) -> " % position for position in positions)),
                " ".join("(fun _e => _f (_e ▸ %sList.Mem.head _%s))" % ("List.Mem.tail _ (" * count, ")" * count)
                         for count in range(len(positions))))
            facts.append("have _pwsn%d : _subset %s %s -> False := fun _h => Exists.elim (%s ([%s] : List %s)) "
                         "(fun _i _f => %s.2 (_h _i %s.1))" % (
                             node, inline(left), inline(right), _UNBOUNDED[index],
                             ", ".join(inline(leaves[position][1]) for position in positions),
                             _component_type(graph, index), proof, proof))
        elif leaves and all(leaf[0] == "value" for leaf in leaves):
            # Maps of constant arrays alone, of Boolean values other than
            # true and false: the rewriter folds the subset to a formula
            # over the values ((subset (const p) (const (not p))) to (not
            # p)), which the subset is at any index.
            names = {leaf: leaf_member(leaf, "_i") for leaf in leaves}
            facts.append("have _pwsv%d : _subset %s %s = (%s -> %s) := propext (Iff.intro "
                         "(fun _h => Nonempty.elim %s (fun _i => _h _i)) (fun _h _ => _h))" % (
                             node, inline(left), inline(right), member(left, names), member(right, names), inhabited))
        # The difference as _subset_eq writes it is the set the rewriter's
        # equality is left with (next to a failure at a stored index too: the
        # rewriter does not pull a store out from under a union).
        key = (sort,) + _essential_table(leaves, difference)
        same = next((candidate for candidate in sets if keys[candidate] == key), None)
        if same is not None and graph.subset_rewrite:
            proof = auxiliary(left, right, "(Iff (And %s (Not %s)) %s)", same)
            facts.append("have _pws%d : _map2 And %s (_map1 Not %s) = %s := funext (fun _i => %s)" % (
                node, inline(left), inline(right), inline(same),
                "rfl" if proof is None else "propext %s" % proof))
    if not members_read:
        return theorems, facts
    # The sides of each equality at the indices the lemma reads from sets of its sort.
    read = {}
    for node in reachable:
        if graph.kind(node) == z3.Z3_OP_SELECT and graph.arguments(node)[0] in tables:
            read.setdefault(graph.decl(graph.arguments(node)[0]).range, set()).add(graph.arguments(node)[1])
    if sum(len(read.get(keys[graph.arguments(node)[0]][0], ())) for node in equalities) > _COMPARISON_READS:
        return theorems, facts
    for node in equalities:
        left, right = graph.arguments(node)
        leaves = sorted(set(tables[left][0]) | set(tables[right][0]))
        for index in sorted(read.get(keys[left][0], ())):
            names = {leaf: leaf_member(leaf, inline(index)) for leaf in leaves}
            facts.append("have _pwr%d_%d : %s = %s -> (Iff %s %s) := fun _h => Iff.of_eq (congrFun _h %s)" % (
                node, index, inline(left), inline(right), member(left, names), member(right, names), inline(index)))
    return theorems, facts


# At most this many read facts per rewrite in _constant_array_comparisons.
_COMPARISON_READS = 64
# Above _COMPARISON_READS, at most this many reads of compared store chains
# (_chain_comparison_reads) per rewrite; past it no read facts are stated.
# They are about n * (n + 2) for two n-store chains at distinct numerals, and
# each is repeated in every case of the rewrite's proof: on iteration 85's
# macOS build two 24-store chains (624 reads) checked in 2.8 s and 1.5 GB,
# 32 stores (1088) in 7.7 s and 3.5 GB, 40 (1680) in 20 s and 7.6 GB, and
# 64 (4224) exceeded the 12 GB watchdog.
_CHAIN_COMPARISON_READS = 640


def _read_count(reads):
    """The number of reads in a map from nodes to their sets of indices."""
    return sum(len(indices) for indices in reads.values())


def _constant_array_comparisons(graph, reachable, atom_indices, variable_indices):
    """Default-value and read facts for a rewrite comparing arrays next to a constant array.

    Z3's rewriter decides an equality between stores over constant arrays
    by the arrays' default values ((= (store (const 0) 1 1) (const 1)) is
    false) or by their values at the stored indices ((= (store (store a 0
    1) 0 0) (store a 0 1)) is false over a = (const 0)); no default or read
    term of the certificate names them. Each such equality implies that the
    default values agree, and the values at each index stored into an array
    of its sort; each store and constant array the rewrite reaches has its
    default value and its value at those indices as facts (_default_store,
    _default_const, _store_apply, _select_const), and at a generic index
    (_Graph.generic) each map its default value too (_default_map_fact: an
    equality the replay ties to an assertion may be false of the default
    values alone, a set equal to a store into its complement). grind chains
    them. The converse of an equality between store chains over constant
    arrays is stated too (_constant_chain_extensionality). The read facts are
    quadratic (indices times arrays), so above _COMPARISON_READS of them
    only the reads the rewriter evaluates in such a comparison are stated
    (_chain_comparison_reads): each side's chain read at the indices stored
    into either side, which the converse's premises need. Those are still
    quadratic in the chains' length, so above _CHAIN_COMPARISON_READS of
    them no read facts are stated at all. The sides of each equality are
    also read at the indices read from their sort (_compared_side_reads),
    unless those reads alone exceed _COMPARISON_READS.

    The default values are those of arrays over Int and Real indices. Over
    another index sort that constant arrays of the certificate are over
    (_Graph.constant_indices: an uninterpreted sort, Bool) there is none,
    and the rewriter does not use one: it compares two constant arrays by
    their values, (= (const v) (const w)) to (= v w), which holds because
    the sort has an index. There each equality implies that its sides
    agree at one index of the sort (_index_witness), where a constant
    array has its value; a store has no fact there, only at the stored
    indices like the others.
    """
    if not any(graph.kind(node) == z3.Z3_OP_CONST_ARRAY for node in reachable):
        return []

    def inline(sub):
        return "(%s)" % _inline(graph, sub, atom_indices, variable_indices)

    def unbounded(node):
        return graph.is_array(node) and _array_components(graph.decl(node).range)[0] in _UNBOUNDED

    def compared_sort(node):
        """Whether node is an array over Int or Real indices, or over another index sort of constant arrays."""
        return unbounded(node) or (graph.is_array(node)
                                   and _array_components(graph.decl(node).range)[0] in graph.constant_indices)

    equalities = [node for node in sorted(reachable)
                  if graph.kind(node) == z3.Z3_OP_EQ and compared_sort(graph.arguments(node)[0])]
    arrays = [node for node in sorted(reachable)
              if graph.kind(node) in (z3.Z3_OP_STORE, z3.Z3_OP_CONST_ARRAY) and compared_sort(node)]
    indices = {}  # array sort -> the indices stored into arrays of that sort
    for node in arrays:
        if graph.kind(node) == z3.Z3_OP_STORE:
            indices.setdefault(graph.decl(node).range, set()).add(graph.arguments(node)[1])
    reads = sum(len(indices.get(graph.decl(node).range, ())) for node in arrays) + sum(
        len(indices.get(graph.decl(graph.arguments(node)[0]).range, ())) for node in equalities)
    if reads > _COMPARISON_READS:
        compared, levels = _chain_comparison_reads(graph, equalities)
        if _read_count(compared) + _read_count(levels) > _CHAIN_COMPARISON_READS:
            compared, levels = {}, {}
    else:
        # Every equality and array at every index stored into its sort.
        compared = {node: indices.get(graph.decl(graph.arguments(node)[0]).range, ()) for node in equalities}
        levels = {node: indices.get(graph.decl(node).range, ()) for node in arrays}
    sides = _compared_side_reads(graph, reachable, equalities)
    if _read_count(sides) <= _COMPARISON_READS:
        levels = {node: set(levels.get(node, ())) | sides.get(node, set()) for node in set(levels) | set(sides)}
    helpers = []
    for node in equalities:
        left, right = (inline(argument) for argument in graph.arguments(node))
        if unbounded(graph.arguments(node)[0]):
            default = "_default %s" % _unbounded(graph, graph.arguments(node)[0])
            helpers.append("  have _e%d : %s = %s -> %s %s = %s %s := congrArg (%s)" % (
                node, left, right, default, left, default, right, default))
        else:
            witness = _index_witness(graph, _array_components(graph.decl(graph.arguments(node)[0]).range)[0])
            helpers.append("  have _e%d : %s = %s -> _select %s %s = _select %s %s :="
                           " congrArg (fun _x => _select _x %s)" % (
                               node, left, right, left, witness, right, witness, witness))
        for index in sorted(compared.get(node, ())):
            helpers.append("  have _e%d_%d : %s = %s -> _select %s %s = _select %s %s :="
                           " congrArg (fun _x => _select _x %s)" % (
                               node, index, left, right, left, inline(index), right, inline(index), inline(index)))
        extensionality = _constant_chain_extensionality(graph, node, inline)
        if extensionality is not None:
            helpers.append("  have _x%d : %s" % (node, extensionality))
        helpers.extend("  have _x%d_%d : %s" % (node, position, statement)
                       for position, statement in enumerate(_ite_chain_extensionality(graph, node, inline)))
    for node in arrays:
        if graph.kind(node) == z3.Z3_OP_STORE:
            arguments = " ".join(inline(argument) for argument in graph.arguments(node))
            if unbounded(node):
                helpers.append("  have _ds%d := %s" % (node, _default_store_fact(graph, node, arguments)))
            helpers.extend("  have _ds%d_%d := _store_apply %s %s" % (node, index, arguments, inline(index))
                           for index in sorted(levels.get(node, ())))
        else:
            value = inline(graph.arguments(node)[0])
            index_type = _array_types(graph, graph.decl(node).range)[0]
            if unbounded(node):
                helpers.append("  have _dc%d := _default_const %s %s" % (
                    node, _unbounded(graph, node, explicit=True), value))
            else:
                helpers.append("  have _dc%d := _select_const (I := %s) %s %s" % (
                    node, index_type, value, _index_witness(graph, _array_components(graph.decl(node).range)[0])))
            helpers.extend("  have _dc%d_%d := _select_const (I := %s) %s %s" % (
                node, index, index_type, value, inline(index))
                           for index in sorted(levels.get(node, ())))
    if graph.generic:
        helpers.extend(_default_map_fact(graph, "_dm%d" % node, node, inline) for node in sorted(reachable)
                       if unbounded(node) and _set_function(graph, node) is not None)
    return helpers


def _compared_side_reads(graph, reachable, equalities):
    """The reads of the store and constant-array sides of equalities at the indices read from their sort.

    An assumed clause tied to the assertions through an unsat core may get
    a cnf lemma that reads an array constant equated to a constant array
    ((or (not (= a (const 1))) (not (= 3 (select a 0))))), with no read term
    of the constant array: the core holds the equality rather than the
    assertion the solver split the clause from. So each store and constant
    array a side of an equality reaches (through ites and down its store
    chain, stopping at a store at that same index term) gets its value at
    every index read from an array of the equality's sort; grind relates
    the read to it by congruence. Returned as a map from those levels to
    their sets of indices, like _chain_comparison_reads's levels.
    """
    read = {}  # array sort -> the indices read from arrays of that sort
    for node in reachable:
        if graph.kind(node) == z3.Z3_OP_SELECT:
            array, index = graph.arguments(node)[:2]
            read.setdefault(graph.decl(array).range, set()).add(index)
    levels = {}
    for node in equalities:
        for index in read.get(graph.decl(graph.arguments(node)[0]).range, ()):
            pending, seen = list(graph.arguments(node)), set()
            while pending:
                current = pending.pop()
                if current in seen:
                    continue
                seen.add(current)
                kind, arguments = graph.kind(current), graph.arguments(current)
                if kind == z3.Z3_OP_ITE:
                    pending.extend(arguments[1:])
                elif kind in (z3.Z3_OP_STORE, z3.Z3_OP_CONST_ARRAY):
                    levels.setdefault(current, set()).add(index)
                    if kind == z3.Z3_OP_STORE and arguments[1] != index:
                        pending.append(arguments[0])
    return levels


def _chain_comparison_reads(graph, equalities):
    """The reads of the store-chain comparisons among equalities: the indices per equality and per array level.

    For (= S T) with S and T store chains over constant arrays (through ites
    of an array with itself, _constant_chain, or ites of such chains, whose
    leaves are all compared at the indices stored into any of them,
    _constant_chain_leaves, when there are at most _ITE_CHAIN_PAIRS pairs
    of leaves, as for _ite_chain_extensionality; above that the equality
    gets no converse, so its reads would only use up the budget of
    _CHAIN_COMPARISON_READS), Z3's rewriter compares S and T
    at every index stored into either chain (array_rewriter::mk_eq_core) and
    evaluates each read down the chain, past the stores at other indices to
    the constant array. So each equality gets those indices, and each store
    and constant array of its chains the indices read through it: all of
    them, except that a read stops at the outermost store at that same index
    term, which the rewriter evaluates to the stored value. The facts grow
    with the compared chains only, not with every array of the sort times
    every stored index.
    """
    compared, levels = {}, {}
    for node in equalities:
        sides = [_constant_chain_leaves(graph, argument) for argument in graph.arguments(node)]
        if None in sides or len(sides[0]) * len(sides[1]) > _ITE_CHAIN_PAIRS:
            continue
        leaves = sides[0] + sides[1]
        indices = {graph.arguments(store)[1] for leaf in leaves for store in _constant_chain(graph, leaf)[1]}
        compared[node] = indices
        for leaf in leaves:
            for index in indices:
                current = leaf
                while True:
                    kind = graph.kind(current)
                    arguments = graph.arguments(current)
                    if kind == z3.Z3_OP_ITE:
                        current = arguments[1]
                        continue
                    levels.setdefault(current, set()).add(index)
                    if kind != z3.Z3_OP_STORE or arguments[1] == index:
                        break
                    current = arguments[0]
    return compared, levels


def _constant_chain(graph, node):
    """The constant array below a chain of stores, and the chain's store nodes outermost first, or None.

    An ite of an array with itself is the array (Z3's rewriter drops it
    before it compares the chains).
    """
    stores = []
    while True:
        kind = graph.kind(node)
        arguments = graph.arguments(node)
        if kind == z3.Z3_OP_STORE:
            stores.append(node)
            node = arguments[0]
        elif kind == z3.Z3_OP_ITE and arguments[1] == arguments[2]:
            node = arguments[1]
        elif kind == z3.Z3_OP_CONST_ARRAY:
            return node, stores
        else:
            return None


def _constant_chain_extensionality(graph, equality, inline):
    """The statement and proof of the converse of an equality between store chains over constant arrays, or None.

    Z3's rewriter decides (= S T), for S and T stores over constant arrays
    (const v) and (const w) with an infinite index sort, by the values of S
    and T at every stored index and by v = w (array_rewriter::mk_eq_core).
    The direction from S = T is congruence (the _e facts of
    _constant_array_comparisons); the converse is extensionality, which
    grind does not do. The fact states it with one premise per stored index
    i, _select S i = _select T i, and proves it by funext, a case split on
    whether the index read is a stored one, and off them _store_off down to
    the constant arrays. Only equalities with at least one store get one.

    The fact is a theorem over any index type, and is stated for the
    equalities over an uninterpreted or Bool index sort of constant arrays
    too (_Graph.constant_indices). There it mirrors no rewrite: over a sort
    that may be finite the rewriter does not decide such an equality this
    way (it expands it into a quantified formula, which the exporter
    rejects).
    """
    sides = [_constant_chain(graph, argument) for argument in graph.arguments(equality)]
    if None in sides or not (sides[0][1] or sides[1][1]):
        return None
    return _chain_pair_extensionality(graph, *graph.arguments(equality), inline)


def _constant_chain_leaves(graph, node):
    """The store chains over constant arrays at the leaves of a tree of array ites, or None if one is not such a chain.

    The leaves are in node order, each once; a chain is a leaf even below
    an ite of it with itself (_constant_chain). Each node is visited once,
    so a tree that shares its ites is walked in linear time.
    """
    leaves, pending, seen = set(), [node], set()
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        if _constant_chain(graph, current) is not None:
            leaves.add(current)
        elif graph.kind(current) == z3.Z3_OP_ITE:
            pending.extend(graph.arguments(current)[1:])
        else:
            return None
    return sorted(leaves)


# The most pairs of leaves (_ite_chain_extensionality) one equality between
# ites of store chains gets a converse for; each fact is a proof by funext
# with one case split per stored index, so they grow with the product of the
# two sides' leaves.
_ITE_CHAIN_PAIRS = 16


def _ite_chain_extensionality(graph, equality, inline):
    """The converses of the comparisons of the leaves of an equality between ites of store chains over constant arrays.

    The sat.smt core may log an asserted (= (ite p S S') T), for S, S', and
    T store chains over constant arrays, as the outcome of comparing each
    branch with T: (= (ite p (store (const x) k y) (const x)) (store (const
    y) 1 x)) as x = y, which the replay ties to the assertion by a rewrite
    step. grind splits the ite but cannot prove a branch equal to T without
    extensionality, and no equality node of the certificate names that
    comparison. So every pair of a leaf of one side with a different leaf of
    the other (_constant_chain_leaves) gets the converse of its comparison
    as _constant_chain_extensionality states it, over the leaves' terms;
    the reads of its premises at the indices stored into either leaf are
    among the read facts (_chain_comparison_reads above the cap). Only
    equalities with an ite of two different arrays on a side get them, and
    at most _ITE_CHAIN_PAIRS pairs; otherwise none.
    """
    arguments = graph.arguments(equality)
    if all(_constant_chain(graph, argument) is not None for argument in arguments):
        return []
    sides = [_constant_chain_leaves(graph, argument) for argument in arguments]
    if None in sides or len(sides[0]) * len(sides[1]) > _ITE_CHAIN_PAIRS:
        return []
    return [_chain_pair_extensionality(graph, left, right, inline)
            for left in sides[0] for right in sides[1] if left != right]


def _chain_pair_extensionality(graph, left_node, right_node, inline):
    """The converse of the comparison of two store chains over constant arrays: their reads at the stored indices
    and the constants' values agree, so the chains are equal (see _constant_chain_extensionality)."""
    sides = [_constant_chain(graph, node) for node in (left_node, right_node)]
    indices = sorted({graph.arguments(store)[1] for _, stores in sides for store in stores})
    hypotheses = {index: "_c%d" % position for position, index in enumerate(indices)}

    def off(node):
        """A proof of (node _j) = v off the stored indices, for v the value of the constant array below node."""
        kind = graph.kind(node)
        arguments = graph.arguments(node)
        if kind == z3.Z3_OP_STORE:
            return "(_store_off %s %s %s _j %s).trans %s" % (
                inline(arguments[0]), inline(arguments[1]), inline(arguments[2]), hypotheses[arguments[1]],
                "(%s)" % off(arguments[0]))
        if kind == z3.Z3_OP_ITE:
            return "(congrFun (ite_self %s) _j).trans (%s)" % (inline(arguments[1]), off(arguments[1]))
        return "rfl"

    left, right = inline(left_node), inline(right_node)
    values = [inline(graph.arguments(constant)[0]) for constant, _ in sides]
    premises = ["_select %s %s = _select %s %s" % (left, inline(index), right, inline(index)) for index in indices]
    names = ["_h%d" % position for position in range(len(indices))]
    tactics = ["intro %s" % " ".join(names + ["_hv"]), "funext _j"]
    for index, name in zip(indices, names):
        tactics.append("by_cases %s : _j = %s" % (hypotheses[index], inline(index)))
        tactics.append("(subst %s; exact %s)" % (hypotheses[index], name))
    first, second = off(left_node), off(right_node)
    tactics.append("exact (%s).trans (_hv.trans (%s).symm)" % (first, second))
    return "%s -> %s = %s := by %s" % (
        " -> ".join(premises + ["%s = %s" % tuple(values)]), left, right, "; ".join(tactics))


def _combination_certified(graph, node):
    """Whether a step is a farkas or bound th-lemma whose coefficients the reconstructor re-derived.

    _check_th_lemma rejects such a step unless its coefficients refute its
    literals (and premises) as linear constraints over the atoms of the
    linear forms, rounding included for an Int bound, so the generalized
    goal of _grind_lemma holds over the atoms alone: it needs none of the
    mod bounds, which only slow omega down (see _grind_lemma). A cut or a
    coefficient-free Int farkas or bound is shape-checked only and keeps them.
    """
    decl = graph.decl(node)
    return decl.name == "th-lemma" and decl.parameters[0] in ("farkas", "bound") and len(decl.parameters) > 1


def _mod_bound_facts(graph, atoms):
    """State 0 <= m < |k| for every mod atom m = (mod t k), then revert the facts into the goal.

    The arithmetic solver fixes these bounds at base level from its mod
    axioms and omits such base-level facts from the lemmas it explains, so
    a cut over mod atoms may rest on them without listing them; generalized
    without them, the atoms are unbounded integers and the lemma unprovable.
    (A combination with coefficients never needs them, see _combination_certified.)
    omega reads % by a positive numeral only, so the facts are the library's.
    Under a negative divisor the upper one is Int.emod_lt, the bound by the
    divisor's absolute value, which decide compares with the numeral |k|:
    that holds however the constant divisor is written ((- 3) is -3, but
    (- (+ 1 2)) is the difference 0 - (1 + 2), see _negation, which a
    rewrite with Int.emod_neg would not match). The facts are best effort:
    should one fail to prove, the generalized attempt fails and the
    fallback runs.
    Returns the have lines and the names of the facts, for the caller to revert.
    """
    lines, names = [], []
    for position, atom in enumerate(atoms):
        if graph.kind(atom) != z3.Z3_OP_MOD:
            continue
        divisor = int(_integer_divisor(graph, atom))
        definitions = " ".join(_definition_names(graph, _reachable(graph, atom)[0]))
        upper = "exact Int.emod_lt_of_pos _ (by decide)"
        if divisor < 0:
            upper = "exact Int.lt_of_lt_of_le (Int.emod_lt _ (by decide)) (by decide)"
        lines.append("have _m%d_0 : ((0 : Int)) <= %s := by unfold %s; exact Int.emod_nonneg _ (by decide)" % (
            position, _term(graph, atom), definitions))
        lines.append("have _m%d_1 : %s < ((%d : Int)) := by unfold %s; %s" % (
            position, _term(graph, atom), abs(divisor), definitions, upper))
        names += ["_m%d_0" % position, "_m%d_1" % position]
    return lines, names


def _atom_bridge_facts(graph, atoms):
    """State the equality of every two atoms with one key (_real_atom_key), to revert before generalizing.

    Z3's rewriter normalizes an ite term (its condition's polarity, the
    branch order, (abs t) to its defining ite), so a rewrite of an
    assertion, or a lemma over both forms, relates atoms that denote one
    value but render differently; generalized apart they are unrelated
    integers and the attempt fails, while splitting every ite (what omega
    and grind do unaided) is exponential in their number. Each equality is
    a two-way split the theory tactic proves on its own; reverted into the
    goal, it survives the generalization as an equation between the fresh
    variables. Returns the have lines and the names of the facts.
    """
    groups = {}
    for atom in atoms:
        # By sort too: in qf_lira an Int and a Real ite over numerals key alike.
        groups.setdefault((graph.decl(atom).range, _real_atom_key(graph, atom)), []).append(atom)
    lines, names = [], []
    for members in groups.values():
        for first, second in zip(members, members[1:]):
            definitions = _definition_names(graph, _reachable(graph, first)[0] | _reachable(graph, second)[0],
                                            (first, second))
            lines.append("have _e%d_%d : %s = %s := by unfold %s; %s" % (
                first, second, _term(graph, first), _term(graph, second), " ".join(definitions),
                _theory_tactic(graph)))
            names.append("_e%d_%d" % (first, second))
    return lines, names


def _opaque_tactic(graph, node):
    """The tactic proving an Int th-lemma over its linear-form atoms generalized, or None.

    A farkas or bound with coefficients is a combination the reconstructor
    re-derived over the atoms (_check_th_lemma), so the generalized goal
    holds and omega, complete for linear integer arithmetic, closes it at
    once. A cut, and a coefficient-free Int farkas or bound (a lattice
    conflict, _lattice_step), lists the bounds and the div and mod rows it
    rests on as literals, except the base-level mod bounds
    (_mod_bound_facts restates them), so the generalized goal holds as
    well when the step is sound, but it needs the integer lattice: grind's
    cutsat module proved a cut over twenty atoms in a second where omega
    took minutes. Neither procedure dominates, though: omega proved a
    25-literal cut over thirteen atoms (seed 67 of random_division_instance
    under a newer solver) in under a second where grind needed between one
    and one and a half million heartbeats. Trying one and falling back to
    the other is not possible, since Lean's `first` does not catch a
    heartbeat timeout (a runtime exception; it fails the whole lemma), so
    such a lemma gets _LATTICE_LEMMA_HEARTBEATS instead (_grind_lemma).
    The arith axioms, euf congruences, and implied equalities keep the
    atoms' definitions.
    """
    parameters = graph.decl(node).parameters
    if parameters[0] not in ("farkas", "bound", "cut") or _lemma_numeric(graph, node) != "Int":
        return None
    return "omega" if len(parameters) > 1 else "grind (splits := 64)"


def _lemma_numeric(graph, node):
    """The arithmetic sort of a theory step: the certificate's, or in a qf_lira certificate the one its atoms share.

    Without a conversion Z3 never combines atoms of the two sorts in one
    arithmetic lemma, and the Int and Real treatments (rounding,
    tightening, omega) differ, so a step over both is rejected. A step
    reaching a conversion (to_real, or to_int and is_int, whose floor
    is an Int atom over a Real term) is _CAST: the sorts meet there, so its
    combination is rational with each Int atom tightened on its own
    (_polarity_constraint), and Lean proves it with both sorts tied
    together (_cast_facts). In a qf_uflira certificate an application of
    an uninterpreted function is an opaque atom of the linear forms, so
    its arguments (of either sort) are not the step's: an Int argument of
    a function with a Real result keeps a step over Real atoms Real. Nor
    are the atoms of an arithmetic ite's condition: an Int ite over a Real
    comparison keeps a step over Int atoms Int.
    Several checks ask about one step, so the answer is kept per node.
    """
    if graph.numeric != _MIXED:
        return graph.numeric
    if node in graph.lemma_sorts:
        return graph.lemma_sorts[node]
    formulas = [graph.conclusion(premise) for premise in graph.arguments(node)[:-1]] + [graph.conclusion(node)]
    sorts, casts = set(), False
    for formula in formulas:
        reachable = _reachable_outside_applications(graph, formula)
        sorts.update(graph.decl(term).range for term in reachable if graph.is_arith(term))
        casts = casts or any(graph.kind(term) in _CONVERSION_KINDS for term in reachable)
    if casts:
        sorts = {_CAST}
    elif len(sorts) > 1:
        raise ReconstructionError("arithmetic step over both Int and Real atoms at node %d" % node)
    graph.lemma_sorts[node] = sorts.pop() if sorts else "Real"
    return graph.lemma_sorts[node]


def _lattice_step(graph, node):
    """Whether node is an Int th-lemma without coefficients: a cut, or a farkas or bound Z3 did not explain."""
    decl = graph.decl(node)
    return (decl.name == "th-lemma" and len(decl.parameters) == 1
            and decl.parameters[0] in ("farkas", "bound", "cut") and _lemma_numeric(graph, node) == "Int")


def _farkas_combination(graph, node):
    """Tactic lines proving an Int farkas or bound th-lemma by the combination its coefficients give, or None.

    The reconstructor re-derived the combination (_check_th_lemma), so the
    proof need not search for one: every premise, and the negation of every
    clause literal, is a bound `lower <= upper` over Int (a strict bound
    tightened by one, an equality oriented by the sign of its multiplier),
    stated as the fact 0 <= upper - lower by a core lemma; the facts scaled
    by their integer multipliers sum to a negative constant, an identity
    checked before any hypothesis is in scope (_sum_identity: `simp +arith`
    first, omega as the fallback), where it only has to normalize the sum,
    a balanced tree (_balanced_sum). With the bounds in scope omega
    searches for the combination itself: two 21-literal Farkas lemmas over twenty variables
    with eight-digit coefficients (QF_LIA cut_lemma_03_012 of z3test's
    smtlib-sample) ran for ten minutes without an answer. Inequality
    multipliers are the hint's coefficients; equality multipliers are solved
    for, as in linear_combination_refutes. A lemma of fewer than
    _FARKAS_COMBINATION_BOUNDS bounds, or with neither a coefficient of
    magnitude _FARKAS_COMBINATION_COEFFICIENT nor a bound over
    _FARKAS_COMBINATION_ATOMS atoms, a combination that needs the integer
    rounding of a bound step (bound_combination_refutes), and any literal
    shape outside the cases below get no attempt: the caller's
    generalized and unfolded proofs remain. Lean checks the attempt like
    any other proof; one that does not elaborate falls through to them.
    """
    if not _combination_certified(graph, node) or _lemma_numeric(graph, node) != "Int":
        return None
    coefficients = [Fraction(parameter) for parameter in graph.decl(node).parameters[1:]]
    if (len(coefficients) != len(graph.arguments(node)) - 1 + len(graph.clause(graph.conclusion(node)))
            or len(coefficients) < _FARKAS_COMBINATION_BOUNDS):
        return None
    lemma = _lemma_bounds(graph, node)
    if lemma is None:
        return None
    premises, bounds = lemma
    if (max((abs(coefficient) for coefficient in coefficients), default=0) < _FARKAS_COMBINATION_COEFFICIENT
            and max(len(bound[5][0]) for bound in bounds) < _FARKAS_COMBINATION_ATOMS):
        return None
    multipliers = _farkas_multipliers([bound[5] for bound in bounds], coefficients, [bound[4] for bound in bounds])
    summed = None if multipliers is None else _combination_sum(bounds, multipliers)
    if summed is None:
        return None
    combination, nonnegative, total, sides = summed
    # The identity goes first, while `simp +arith` (and omega, its fallback)
    # sees no hypothesis but the valuation, over the atoms of the linear
    # forms left folded (delta unfolds the sums, products, and numerals
    # above them in one pass, and both read a folded `term_N _atoms _vars`
    # atom as one opaque variable). The rest is one
    # term, typed by the ascription of the sum: a tactic `have` per fact
    # cost Lean about two megabytes per lemma, which a certificate of 800
    # two-literal Farkas lemmas (the wide division seed) could not afford.
    return [
        _sum_identity(graph, "_sum", combination, total, sides),
        "exact %sClassical.byContradiction fun _hn => %s" % (
            "".join("fun _p%d => " % position for position in range(premises)),
            _combination_absurd(nonnegative, combination, "_sum")),
    ]


def _polynomial_certificate(graph, node):
    """The polynomial refutation of an Int th-lemma over products, or None: (premises, bounds, refutation).

    The bounds are those the premises and negated clause literals state
    (_lemma_bounds); each is the fact 0 <= form, or form = 0 for an
    equality, whose form is a polynomial over the atoms of the linear forms
    that are no products once the product atoms are multiplied out. The
    refutation (proof_certificate.polynomial_refutation) multiplies pairs of
    these facts and sums the products to a negative constant. A lemma with a
    disequality or another literal outside _lemma_bounds, without a product,
    or without a refutation within the search's bounds has none. The search
    calls z3, so the answer is kept per node.
    """
    if node not in graph.polynomial_certificates:
        graph.polynomial_certificates[node] = None
        try:
            lemma = (_lemma_bounds(graph, node) if graph.integer_products and _lemma_numeric(graph, node) == "Int"
                     else None)
        except ReconstructionError:
            lemma = None  # a cnf lemma over both sorts, or over a term the linear forms do not read
        if lemma is not None:
            try:
                facts = [(bound[4], expand_polynomial(bound[5][0], bound[5][1],
                                                      lambda atom: _product_parts(graph, atom)))
                         for bound in lemma[1]]
            except (ProofExportError, ReconstructionError):
                facts = []  # too many monomials, or a factor the linear forms do not read
            refutation = polynomial_refutation(facts)
            if refutation is not None:
                graph.polynomial_certificates[node] = lemma + (refutation,)
    return graph.polynomial_certificates[node]


def _product_parts(graph, atom):
    """The linear forms (terms, constant) of the factors of a product atom, None for another atom (expand_polynomial)."""
    if graph.kind(atom) != z3.Z3_OP_MUL:
        return None
    parts = []
    for argument in graph.arguments(atom):
        terms = {}
        constant = _linear_term(graph, argument, Fraction(1), terms)
        parts.append((terms, constant))
    return parts


def _product_combination(graph, node):
    """Tactic lines proving an Int th-lemma over products by its polynomial refutation, or None.

    For an nla th-lemma (_check_th_lemma requires the refutation), for a
    cut or a coefficient-free farkas or bound (_lattice_step) over products
    (a simplex conflict that rests on a bound the nonlinear solver
    propagated, 0 <= (* m m) say, is logged as one), and for a cnf lemma
    whose literals are such bounds (_cnf_lemma). The proof is that of
    _farkas_combination with products among the summands: every fact 0 <=
    upper - lower of the lemma (_lemma_bounds) is proved by a core lemma,
    the product of two nonnegative facts is nonnegative by Int.mul_nonneg,
    the square of an atom by a case split on its sign, and a product with
    an equality's upper - lower = 0 is zero by Int.mul_eq_zero; the
    products scaled by their integer multipliers sum to a negative constant,
    an identity of polynomials over the folded atoms that grind's ring
    normalization proves before any hypothesis is in scope. Lean checks the
    attempt like any other proof; one that does not elaborate falls through
    to the caller's generalized and unfolded proofs.
    """
    parameters = graph.decl(node).parameters
    if parameters[0] not in ("nla", "cnf") and not _lattice_step(graph, node):
        return None
    certificate = _polynomial_certificate(graph, node)
    if certificate is None:
        return None
    premises, bounds, refutation = certificate
    sides = set()

    def render(derivation):
        """(expression, proof, zero): the proof shows expression = 0 when zero, 0 <= expression otherwise."""
        if derivation[0] == "fact":
            lower, upper, tightened, proof, equality, _, structure = bounds[derivation[1]]
            sides.update(structure)
            expression = "(%s - %s)" % (upper, "(%s + 1)" % lower if tightened else lower)
            if equality:
                return expression, "(Int.sub_eq_zero_of_eq (Eq.symm %s))" % proof, True
            return expression, "(Int.sub_nonneg_of_le %s)" % proof, False
        if derivation[0] == "atom":
            return _term(graph, derivation[1]), None, False
        if derivation[0] == "square":
            atom = _term(graph, derivation[1])
            return "(%s * %s)" % (atom, atom), (
                "((Int.le_total ((0 : Int)) %s).elim (fun _s => Int.mul_nonneg _s _s) "
                "(fun _s => Int.mul_nonneg_of_nonpos_of_nonpos _s _s))" % atom), False
        left, left_proof, left_zero = render(derivation[1])
        right, right_proof, right_zero = render(derivation[2])
        expression = "(%s * %s)" % (left, right)
        if left_zero or right_zero:
            return expression, "(Int.mul_eq_zero.mpr (%s %s))" % (
                "Or.inl" if left_zero else "Or.inr", left_proof if left_zero else right_proof), True
        return expression, "(Int.mul_nonneg %s %s)" % (left_proof, right_proof), False

    scale = functools.reduce(math.lcm, (multiplier.denominator for multiplier, _ in refutation), 1)
    summands, proofs = [], []
    for multiplier, derivation in refutation:
        expression, proof, zero = render(derivation)
        summands.append("((%d : Int)) * %s" % (multiplier * scale, expression))
        proofs.append("(Int.le_of_eq (Eq.symm (Int.mul_eq_zero.mpr (Or.inr %s))))" % proof if zero
                      else "(Int.mul_nonneg (by decide) %s)" % proof)
    combination, nonnegative = _balanced_sum(summands, proofs)
    # The refutation sums to -1 (polynomial_refutation), so the scaled one to -scale.
    return [
        "have _sum : %s = ((%d : Int)) := by %sgrind" % (
            combination, -scale, "delta %s; " % " ".join(_definition_names(graph, sides)) if sides else ""),
        "exact %sClassical.byContradiction fun _hn => %s" % (
            "".join("fun _p%d => " % position for position in range(premises)),
            _combination_absurd(nonnegative, combination, "_sum")),
    ]


# The connectives a step proved by the signs of its factors may have around its comparisons (_sign_split).
_SIGN_SPLIT_CONNECTIVES = (z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_NOT, z3.Z3_OP_IFF, z3.Z3_OP_EQ, z3.Z3_OP_IMPLIES,
                           z3.Z3_OP_XOR, z3.Z3_OP_ITE, z3.Z3_OP_TRUE, z3.Z3_OP_FALSE)
_SIGN_STATEMENTS = {-1: "%s < ((0 : Int))", 0: "%s = ((0 : Int))", 1: "((0 : Int)) < %s"}
_SIGN_LEMMAS = {(1, 1): "Int.mul_pos", (-1, -1): "Int.mul_pos_of_neg_of_neg",
                (1, -1): "Int.mul_neg_of_pos_of_neg", (-1, 1): "Int.mul_neg_of_neg_of_pos"}


def _comparison_polynomial(graph, formula):
    """The polynomial of left - right of a comparison of Int terms, its product atoms multiplied out, or None."""
    arguments = graph.arguments(formula)
    if ((graph.kind(formula) not in _ARITH_PREDICATE_NAMES and graph.kind(formula) != z3.Z3_OP_EQ)
            or len(arguments) != 2
            or not all(graph.is_arith(argument) and graph.is_int(argument) for argument in arguments)):
        return None
    terms = {}
    try:
        constant = (_linear_term(graph, arguments[0], Fraction(1), terms)
                    + _linear_term(graph, arguments[1], Fraction(-1), terms))
        polynomial = expand_polynomial(terms, constant, lambda atom: _product_parts(graph, atom))
    except (ProofExportError, ReconstructionError):
        return None  # a term the linear forms do not read, or too many monomials
    if any(value.denominator != 1 for value in polynomial.values()):
        return None
    return polynomial


def _common_factors(polynomial):
    """Factor the atoms every nonconstant monomial shares out of a polynomial, or None when there is none.

    Returns (factors, quotient, constant) with polynomial = the product of
    factors (atoms, repeated as often as every monomial has them) * quotient
    + constant.
    """
    monomials = {monomial: value for monomial, value in polynomial.items() if monomial}
    common = None
    for monomial in monomials:
        common = Counter(monomial) if common is None else common & Counter(monomial)
    if not common:
        return None
    quotient = {tuple(sorted((Counter(monomial) - common).elements())): value
                for monomial, value in monomials.items()}
    return sorted(common.elements()), quotient, polynomial.get((), Fraction(0))


def _polynomial_shape(polynomial):
    """The nonconstant monomials of a polynomial up to a common factor: what normalizing a comparison keeps."""
    monomials = sorted((monomial, value) for monomial, value in polynomial.items() if monomial)
    return tuple((monomial, value / monomials[0][1]) for monomial, value in monomials)


def _compares_with_zero(kind, polynomial):
    """Whether a comparison of Int terms, normalized as Z3's rewriter does, compares its monomials with zero.

    Those are the comparisons the rewriter splits by the signs of their
    factors (factor_le_ge_eq asks for a zero right side). kind is the
    comparison's (Z3_OP_LE, GE, LT, GT, or EQ) and the polynomial that of
    left - right, g v + d with g the gcd of its coefficients: the
    rewriter divides by g and rounds the constant, g v + d <= 0 to v <=
    floor(-d / g) and g v + d >= 0 to v >= ceil(-d / g), a strict comparison
    being the negation of the opposite one ((<= (* 2 (* m n)) 1) is (<= (* m
    n) 0)); an equation keeps its constant.
    """
    coefficients = [abs(int(value)) for monomial, value in polynomial.items() if monomial]
    if not coefficients:
        return False
    divisor, constant = functools.reduce(math.gcd, coefficients), polynomial.get((), Fraction(0))
    if kind == z3.Z3_OP_EQ:
        return constant == 0
    if kind in (z3.Z3_OP_LE, z3.Z3_OP_GT):
        return -divisor < constant <= 0
    return 0 <= constant < divisor


def _polynomial_text(graph, polynomial):
    """An Int polynomial over atoms of the linear forms as a Lean sum of multiples of products of the folded atoms."""
    summands = []
    for monomial, value in sorted(polynomial.items()):
        summands.append("((%d : Int))" % value)
        if monomial:
            # The product of the atoms as Lean reads a binary (* a b): omega takes it for the same atom.
            product = functools.reduce(lambda right, atom: "(%s * %s)" % (_term(graph, atom), right),
                                       reversed(monomial[:-1]), _term(graph, monomial[-1]))
            summands[-1] = "(%s * %s)" % (summands[-1], product)
    return "(%s)" % " + ".join(summands)


def _sign_split(graph, node, rewrite=False):
    """Tactic lines proving a step over Int comparisons of products by the signs of their factors, or None.

    Z3's rewriter decides a comparison of a polynomial with zero by the
    signs of its factors (arith_rewriter.cpp, factor_le_ge_eq: with f a
    factor of every monomial of p and p = f * g, p >= 0 becomes (or (= (>= f
    0) (>= g 0)) (= f 0) (= g 0)), p <= 0 and p = 0 alike, g rewritten the
    same way and the linear comparisons normalized, over Int with their
    rounding): (>= (+ (* -2 m) (* -3 (* n m))) 0) becomes (or (= 0 m) (= (<=
    0 m) (<= n -1))). Neither omega, to which a product is an opaque atom,
    nor grind proves that.

    The proof (_sign_cases) redoes the factoring, not the rewriter's
    choices. In a rewrite step it factors every comparison of the rewritten
    side (the left) over a product that the other side does not keep; in a
    cnf lemma that is one theory fact (an assertion over a product implies
    a clause over its factors, when Z3 logs the clause in the rewriter's
    form) every comparison over a product. The proof reads comparisons of
    Int terms under propositional connectives; any other formula there (a
    predicate application next to the product) is an atom it leaves folded. A
    step that needs more than the signs ((= (* m m) 3) to false) fails the
    attempt at its first leaf, and Lean falls through to the proofs of
    _grind_lemma, as for any other structural attempt.
    """
    if not graph.integer_products:
        return None
    conclusion = graph.conclusion(node)
    polynomials, outside = {}, {conclusion}

    def comparisons(root):
        """The comparisons of Int terms under the connectives of a formula, or None for a term.

        Any other formula under the connectives (a predicate application,
        an ite of formulas, a distinct, a comparison of other terms) is an
        atom of the goal's propositional structure: its definition stays
        folded, as the atoms of the linear forms do.
        """
        found, pending, seen = [], [root], set()
        while pending:
            formula = pending.pop()
            if formula in seen:
                continue
            seen.add(formula)
            arguments = graph.arguments(formula)
            if graph.is_term(formula):
                return None
            if arguments and graph.is_term(arguments[0]):
                polynomial = _comparison_polynomial(graph, formula)
                if polynomial is not None:
                    polynomials[formula] = polynomial
                    outside.add(formula)
                    found.append(formula)
            elif graph.kind(formula) in _SIGN_SPLIT_CONNECTIVES or (
                    graph.kind(formula) == z3.Z3_OP_UNINTERPRETED and not arguments):
                outside.add(formula)
                pending.extend(arguments)
        return sorted(found)

    def shape(atom):
        return _polynomial_shape(polynomials[atom]), _compares_with_zero(graph.kind(atom), polynomials[atom])

    if rewrite:
        left, right = _equivalence(graph, conclusion, "rewrite")
        rewritten, kept = comparisons(left), comparisons(right)
        if rewritten is None or kept is None:
            return None
        # A comparison the rewriter only normalized keeps its monomials up
        # to a common factor, and compares them with zero only if it did
        # before: (>= (* m n) 7) kept on the right side says nothing about
        # a (<= (* m n) 0) on the left, which the rewriter split.
        shapes = {shape(atom) for atom in kept}
        candidates = [atom for atom in rewritten if shape(atom) not in shapes]
    else:
        candidates = comparisons(conclusion)
        if candidates is None:
            return None
    lines = _sign_cases(graph, polynomials, outside, [
        atom for atom in candidates if any(len(monomial) > 1 for monomial in polynomials[atom])])
    # _grind_lemma unfolds the goal outside its opaque atoms before any
    # attempt when it has such atoms: the proof starts from the folded goal.
    return lines and ["show %s" % _formula(graph, conclusion)] + lines


def _sign_split_clause(graph, structure):
    """Tactic lines proving a theory clause of a cnf lemma by the signs of the factors of its products, or None.

    A clause over the leaves of a cnf lemma (_theory_clauses) may relate a
    product to its factors, as the rewriter's sign split does when Z3 logs
    a conjunct's clause in its rewritten form: 0 < m * n and 0 <= m give 0
    <= n. Every leaf of the clause must be a comparison of Int terms; those
    over products are factored (_sign_cases).
    """
    if not graph.integer_products:
        return None
    leaves, pending = set(), [structure]
    while pending:
        current = pending.pop()
        if current[0] == "leaf":
            leaves.add(current[1])
        pending.extend(_structure_children(current))
    polynomials = {leaf: _comparison_polynomial(graph, leaf) if leaf >= 0 else None for leaf in leaves}
    if not leaves or None in polynomials.values():
        return None  # a pair leaf of a distinct, or a leaf that is no comparison of Int terms
    return _sign_cases(graph, polynomials, set(leaves), [
        leaf for leaf in sorted(leaves) if any(len(monomial) > 1 for monomial in polynomials[leaf])])


def _sign_cases(graph, polynomials, outside, candidates):
    """Tactic lines proving a goal over comparisons of Int terms by the signs of the factors of its products, or None.

    polynomials maps every comparison s ~ t of the goal to the polynomial
    of s - t (_comparison_polynomial), outside holds the other definitions
    of the goal above its comparisons, and candidates are the comparisons
    to factor. From each one whose nonconstant monomials share an atom,
    those atoms are factored out: s - t = c * (f1 * (... * fn)) + d, the
    last factor the quotient polynomial unless it is the constant c. That
    identity of polynomials over the folded atoms is proved by grind's ring
    normalization before any hypothesis is in scope (as in
    _product_combination). Then the factors are split by Int.lt_trichotomy,
    three cases each; in every case the sign of each product follows from
    those of its factors (Int.mul_pos and its three variants;
    Int.mul_eq_zero once a factor is zero, the factors after it unsplit),
    and with the identities, the factors' signs, and the products' signs in
    scope the goal is linear arithmetic over the atoms and the products as
    written: the certificate's own tactic for theory steps
    (_theory_tactic). None without a product to factor or with more than
    _SIGN_SPLIT_FACTORS factors to split on, and None when every candidate
    equates one monomial with zero: (= (* m n) 0) is (or (= m 0) (= n 0)) by
    Int.mul_eq_zero, which the step's own grind is given (_theory_tactic)
    and which costs one line where the split of five factors costs 63 leaves.
    """
    if all(graph.kind(atom) == z3.Z3_OP_EQ and len(polynomials[atom]) == 1 for atom in candidates):
        return None
    outside = set(outside)
    for atom in polynomials:
        for side in graph.arguments(atom):
            outside |= _linear_structure(graph, side)
    expressions, products, lines, names = [], [], [], []
    squares = {monomial[0] for polynomial in polynomials.values() for monomial in polynomial
               if len(monomial) == 2 and monomial[0] == monomial[1]}
    for atom in candidates:
        factored = _common_factors(polynomials[atom])
        if factored is None:
            continue
        factors, quotient, constant = factored
        texts = [_term(graph, factor) for factor in factors]
        coefficient = 1
        if set(quotient) == {()}:
            coefficient = quotient[()]
        else:
            texts.append(_polynomial_text(graph, quotient))
            squares.update(monomial[0] for monomial in quotient if len(monomial) == 2 and monomial[0] == monomial[1])
        if len(texts) < 2:
            continue  # a linear comparison: nothing to factor
        for text in texts:
            if text not in expressions:
                expressions.append(text)
        product = texts[-1]
        for text in reversed(texts[:-1]):
            product = "(%s * %s)" % (text, product)
        sides = graph.arguments(atom)
        structure = _linear_structure(graph, sides[0]) | _linear_structure(graph, sides[1])
        names.append("_i%d" % len(products))
        lines.append("have %s : %s - %s = ((%d : Int)) * %s + ((%d : Int)) := by delta %s; grind" % (
            names[-1], _term(graph, sides[0]), _term(graph, sides[1]), coefficient, product, constant,
            " ".join(_definition_names(graph, structure))))
        products.append(([expressions.index(text) for text in texts], product))
    if not products or len(expressions) > _SIGN_SPLIT_FACTORS:
        return None
    # The identities are stated folded and reverted, so the unfold rewrites
    # them as it rewrites the goal; the atoms of the linear forms stay folded.
    lines += ["revert " + " ".join(names), "unfold " + " ".join(_definition_names(graph, outside)),
              "intro " + " ".join(names)]
    # The square of an atom the goal compares is nonnegative, whatever the atom's sign.
    lines += ["have _q%d : ((0 : Int)) <= (%s * %s) := (Int.le_total ((0 : Int)) %s).elim "
              "(fun _h => Int.mul_nonneg _h _h) (fun _h => Int.mul_nonneg_of_nonpos_of_nonpos _h _h)" % (
                  position, _term(graph, atom), _term(graph, atom), _term(graph, atom))
              for position, atom in enumerate(sorted(squares))]
    # grind for the leaves omega cannot close: a product written in another
    # order than in the comparison factored, or a product in the quotient.
    tactic = "(%s)" % _theory_tactic(graph)

    def sign(factors, signs):
        """The sign of a product of factors under the signs split so far and its proof, or None while undecided."""
        zero = next((position for position, factor in enumerate(factors) if signs.get(factor) == 0), None)
        if zero is not None:
            proof = "_s%d" % factors[zero]
            if zero < len(factors) - 1:
                proof = "(Int.mul_eq_zero.mpr (Or.inl %s))" % proof
            return 0, functools.reduce(lambda inner, _: "(Int.mul_eq_zero.mpr (Or.inr %s))" % inner,
                                       range(zero), proof)
        if any(factor not in signs for factor in factors):
            return None
        value, proof = signs[factors[-1]], "_s%d" % factors[-1]
        for factor in reversed(factors[:-1]):
            proof = "(%s _s%d %s)" % (_SIGN_LEMMAS[signs[factor], value], factor, proof)
            value *= signs[factor]
        return value, proof

    def cases(signs, indent):
        decided = [sign(factors, signs) for factors, _ in products]
        pad = " " * indent
        if None not in decided:
            for position, ((value, proof), (_, product)) in enumerate(zip(decided, products)):
                lines.append("%shave _e%d : %s := %s" % (pad, position, _SIGN_STATEMENTS[value] % product, proof))
            lines.append(pad + tactic)
            return
        split = next(factor for (factors, _), value in zip(products, decided) if value is None
                     for factor in factors if factor not in signs)
        lines.append("%srcases Int.lt_trichotomy %s ((0 : Int)) with _s%d | _s%d | _s%d" % (
            pad, expressions[split], split, split, split))
        for value in (-1, 0, 1):
            first = len(lines)
            cases({**signs, split: value}, indent + 2)
            lines[first] = "%s· %s" % (pad, lines[first][indent + 2:])

    cases({}, 0)
    return lines


def _sum_identity(graph, name, combination, total, sides):
    """The tactic line stating that a combination of facts sums to its constant.

    The identity is linear arithmetic without hypotheses, so the linear
    normalization of `simp +arith` decides it, with omega as the fallback.
    omega alone is quadratic here: the 202-bound combination of QF_LIA
    bofill-scheduling ex11200_2600_100 (428 atoms) took it about five million
    heartbeats, past the lemma's budget, and an exhausted budget is not an
    error `first` catches, so the unfolded fallback never ran; `simp +arith`
    took about two seconds.
    """
    return "have %s : %s = ((%d : Int)) := by %sfirst | (simp +arith only []; done) | omega" % (
        name, combination, total, "delta %s; " % " ".join(_definition_names(graph, sides)) if sides else "")


def _combination_absurd(nonnegative, combination, identity):
    """The proof of False from 0 <= combination (nonnegative) and the identity combination = a negative constant."""
    return "absurd (Int.le_trans (%s : ((0 : Int)) <= %s) (Int.le_of_eq %s)) (by decide)" % (
        nonnegative, combination, identity)


def _lemma_bounds(graph, node):
    """The bounds an Int th-lemma's premises and negated clause literals state, or None.

    Returns the number of premises and the bounds, each a tuple (lower,
    upper, tightened, proof, equality, form, structure) with lower and
    upper rendered: proof shows lower <= upper (lower + 1 <= upper when
    tightened, lower = upper for an equality) from the premises _p0, ...
    and the negated clause _hn of the caller's proof, form is the linear
    form (terms, constant) of the fact 0 <= upper - lower (- 1 when
    tightened) over the atoms, and structure the term nodes above the
    atoms (_linear_structure). A disequality bounds nothing, so a lemma
    with one, or with a literal outside the shapes below, gets None.
    """
    premises = [graph.conclusion(premise) for premise in graph.arguments(node)[:-1]]
    literals = graph.clause(graph.conclusion(node))
    # (atom, holds, evidence): evidence proves the atom, or its negation when it does not hold.
    evidence = [(premise, True, "_p%d" % position) for position, premise in enumerate(premises)]
    for position, literal in enumerate(literals):
        evidence.append((literal, False, "(fun _h => _hn %s)" % _inject(position, len(literals), "_h")))
    bounds = []  # (lower, upper, tightened, proof of lower <= upper given the oriented evidence, equality)
    for atom, holds, proof in evidence:
        if graph.kind(atom) == z3.Z3_OP_NOT:
            atom, holds = graph.arguments(atom)[0], not holds
            if holds:
                # Not (Not atom): the literal (not atom) is false, so the atom holds.
                proof = "(Classical.byContradiction %s)" % proof
        kind, arguments = graph.kind(atom), graph.arguments(atom)
        if (kind not in _ARITH_PREDICATE_NAMES and kind != z3.Z3_OP_EQ) or not graph.is_arith(arguments[0]):
            return None
        left, right = arguments
        if kind in (z3.Z3_OP_GE, z3.Z3_OP_GT):
            # a >= b is b <= a by definition (GE.ge is reducible), and a > b is b < a.
            left, right, kind = right, left, {z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_GT: z3.Z3_OP_LT}[kind]
        if kind == z3.Z3_OP_EQ:
            if not holds:
                return None  # A disequality bounds nothing.
            bounds.append((left, right, False, proof, True))
        elif holds and kind == z3.Z3_OP_LE:
            bounds.append((left, right, False, proof, False))
        elif holds:
            bounds.append((left, right, True, "(Int.lt_iff_add_one_le.mp %s)" % proof, False))
        elif kind == z3.Z3_OP_LE:
            bounds.append((right, left, True, "(Int.lt_iff_add_one_le.mp (Int.not_le.mp %s))" % proof, False))
        else:
            bounds.append((right, left, False, "(Int.not_lt.mp %s)" % proof, False))
    rendered = []
    for lower, upper, tightened, proof, equality in bounds:
        terms = {}
        constant = (_linear_term(graph, upper, Fraction(1), terms) + _linear_term(graph, lower, Fraction(-1), terms)
                    - (1 if tightened else 0))
        rendered.append((_term(graph, lower), _term(graph, upper), tightened, proof, equality,
                         ({key: value for key, value in terms.items() if value}, constant),
                         _linear_structure(graph, lower) | _linear_structure(graph, upper)))
    return len(premises), rendered


def _combination_sum(bounds, multipliers):
    """The facts 0 <= upper - lower of bounds (_lemma_bounds) scaled by multipliers and summed, or None.

    Returns the sum, the proof that it is nonnegative, its constant (the
    multipliers scaled to integers), and the term nodes to delta in its
    identity, or None unless the constant is negative and every negative
    multiplier is an equality's.
    """
    scale = functools.reduce(math.lcm, (multiplier.denominator for multiplier in multipliers), 1)
    summands, proofs, sides, total = [], [], set(), Fraction(0)
    for (lower, upper, tightened, proof, equality, (_, constant), structure), multiplier in zip(bounds, multipliers):
        if multiplier == 0:
            continue
        total += multiplier * constant
        if multiplier < 0:
            # Only an equality takes a negative multiplier: use it the other way round.
            if not equality:
                return None
            lower, upper, proof, multiplier = upper, lower, "(Eq.symm %s)" % proof, -multiplier
        if equality:
            proof = "(Int.le_of_eq %s)" % proof
        sides |= structure
        rendered_lower = "(%s + 1)" % lower if tightened else lower
        difference = "(%s - %s)" % (upper, rendered_lower)
        summands.append("((%d : Int)) * %s" % (multiplier * scale, difference))
        proofs.append("(Int.mul_nonneg (by decide) (Int.sub_nonneg_of_le %s))" % proof)
    if not summands or total >= 0 or (total * scale).denominator != 1:
        return None
    combination, nonnegative = _balanced_sum(summands, proofs)
    return combination, nonnegative, int(total * scale), sides


def _balanced_sum(summands, proofs):
    """The sum of summands as a balanced tree, and its proof of 0 <= sum from proofs of 0 <= summand.

    Normalizing a sum costs omega and `simp +arith` the size of each partial
    sum: right-nested, the 202 summands of a wide Farkas combination made
    that quadratic in the summands and atoms (_sum_identity).
    """
    if len(summands) == 1:
        return summands[0], proofs[0]
    middle = (len(summands) + 1) // 2
    left, left_proof = _balanced_sum(summands[:middle], proofs[:middle])
    right, right_proof = _balanced_sum(summands[middle:], proofs[middle:])
    return "(%s + %s)" % (left, right), "(Int.add_nonneg %s %s)" % (left_proof, right_proof)


def _split_combination(graph, node):
    """Tactic lines proving an Int lattice lemma by one split and two combinations, or None.

    A cut, and a farkas or bound without coefficients (_lattice_step),
    states a clause whose negation has no integer solution, though it may
    have a rational one: the hint names the bounds but not the cut's
    derivation, so omega and grind redo the search, and a cut over twenty
    variables (QF_LIA cut_lemmas) ran for minutes or exhausted Lean's
    memory. Every Gomory cut is a split cut: for some integer form s and
    integer k, each side of s <= k or k + 1 <= s, with the bounds
    (_lemma_bounds), has a rational combination refuting it. z3 searches
    for s, k, and both combinations as one mixed integer problem
    (_split_certificate) within a resource limit, the coefficients of s
    bounded first (_SPLIT_MAGNITUDES); nothing it returns is
    trusted: Python checks the combinations, and Lean checks the case
    split on Int.lt_or_le and each combination as in _farkas_combination.
    A lemma without a certificate gets no attempt, and one that does not
    elaborate falls through to the generalized and unfolded proofs.
    """
    if not _lattice_step(graph, node):
        return None
    lemma = _lemma_bounds(graph, node)
    if lemma is None:
        return None
    premises, bounds = lemma
    for magnitude in _SPLIT_MAGNITUDES:
        certificate = _split_certificate([bound[5] for bound in bounds], [bound[4] for bound in bounds], magnitude)
        if certificate is not None:
            break
    else:
        return None
    split, bound, below, above = certificate
    form = " + ".join("((%d : Int)) * %s" % (coefficient, _term(graph, key))
                      for key, coefficient in sorted(split.items())) or "((0 : Int))"
    form, limit = "(%s)" % form, "((%d : Int))" % bound
    # The side k < s, tightened to k + 1 <= s, and the side s <= k, each a
    # fact 0 <= upper - lower over the atoms.
    facts = [((limit, form, True, "(Int.lt_iff_add_one_le.mp _s)", False, (split, -bound - 1), set()), above),
             ((form, limit, False, "_s", False, ({key: -value for key, value in split.items()}, bound), set()),
              below)]
    lines, branches = [], []
    for position, (fact, multipliers) in enumerate(facts):
        summed = _combination_sum(bounds + [fact], multipliers + [Fraction(1)])
        if summed is None:
            return None
        combination, nonnegative, total, structure = summed
        lines.append(_sum_identity(graph, "_sum%d" % position, combination, total, structure))
        branches.append("(fun _s => %s)" % _combination_absurd(nonnegative, combination, "_sum%d" % position))
    lines.append("exact %sClassical.byContradiction fun _hn => (Int.lt_or_le %s %s).elim %s %s" % (
        "".join("fun _p%d => " % position for position in range(premises)), limit, form, *branches))
    return lines


def _split_certificate(forms, equalities, magnitude=None):
    """A split refuting the facts 0 <= form over Int, by z3, or None: (s, k, below, above).

    s maps atoms to integer coefficients, of at most magnitude when given,
    and k is an integer; below are
    multipliers (nonnegative except an equality's) summing the facts and
    k - s >= 0 to a negative constant with every atom cancelled, above the
    same for the facts and s - k - 1 >= 0. The model is checked here, so a
    wrong one gives None, as does a problem z3 does not solve within
    _SPLIT_BOUNDED_RLIMIT, or _SPLIT_RLIMIT when unbounded (deterministic,
    unlike a timeout).
    """
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("rlimit", _SPLIT_RLIMIT if magnitude is None else _SPLIT_BOUNDED_RLIMIT)
    keys = sorted({key for terms, _ in forms for key in terms})
    split = {key: z3.Int("s%d" % key, context) for key in keys}
    if magnitude is not None:
        solver.add(*[z3.And(-magnitude <= variable, variable <= magnitude) for variable in split.values()])
    bound = z3.Int("k", context)
    below = [z3.Real("b%d" % position, context) for position in range(len(forms))]
    above = [z3.Real("a%d" % position, context) for position in range(len(forms))]

    def rational(number):
        return z3.RealVal(str(number), context)

    for position, equality in enumerate(equalities):
        if not equality:
            solver.add(below[position] >= 0, above[position] >= 0)
    for key in keys:
        uses = [(position, terms[key]) for position, (terms, _) in enumerate(forms) if key in terms]
        solver.add(z3.Sum([below[position] * rational(factor) for position, factor in uses]) == split[key])
        solver.add(z3.Sum([above[position] * rational(factor) for position, factor in uses]) == -split[key])
    solver.add(z3.Sum([below[position] * rational(constant) for position, (_, constant) in enumerate(forms)])
               + bound < 0)
    solver.add(z3.Sum([above[position] * rational(constant) for position, (_, constant) in enumerate(forms)])
               - bound - 1 < 0)
    if solver.check() != z3.sat:
        return None
    model = solver.model()

    def number(variable):
        result = model.eval(variable, model_completion=True)
        if z3.is_int_value(result):
            return Fraction(result.as_long())
        return Fraction(result.numerator_as_long(), result.denominator_as_long())

    split = {key: int(number(variable)) for key, variable in split.items()}
    split = {key: coefficient for key, coefficient in split.items() if coefficient}
    bound = int(number(bound))
    below, above = [number(variable) for variable in below], [number(variable) for variable in above]
    for multipliers, (total, constant) in ((below, ({key: -value for key, value in split.items()}, bound)),
                                           (above, (dict(split), -bound - 1))):
        for (terms, form_constant), multiplier in zip(forms, multipliers):
            constant += multiplier * form_constant
            for key, factor in terms.items():
                total[key] = total.get(key, 0) + multiplier * factor
        if any(total.values()) or constant >= 0 or any(
                multiplier < 0 for multiplier, equality in zip(multipliers, equalities) if not equality):
            return None
    return split, bound, below, above


def _linear_structure(graph, node):
    """The term nodes of a linear form above its atoms (_linear_term), the atoms excluded."""
    structure, pending = set(), [node]
    while pending:
        node = pending.pop()
        if node in structure or graph.kind(node) in _LINEAR_ATOM_KINDS:
            continue
        structure.add(node)
        pending.extend(graph.arguments(node))
    return structure


# Reads of arrays, extensionality witnesses, and default values over Int or
# Real are atoms too.
_LINEAR_ATOM_KINDS = (z3.Z3_OP_UNINTERPRETED, z3.Z3_OP_ITE, z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM, z3.Z3_OP_ABS,
                      z3.Z3_OP_TO_INT, z3.Z3_OP_SELECT, z3.Z3_OP_ARRAY_EXT,
                      z3.Z3_OP_ARRAY_DEFAULT)


def _farkas_multipliers(forms, coefficients, equalities):
    """Multipliers summing the facts 0 <= form to a negative constant, or None.

    forms are (terms, constant) pairs; an inequality's multiplier is its
    coefficient (nonnegative), an equality's (a fact both ways) is solved
    for, any sign, so that the variables cancel. Equalities inconsistent on
    their own refute alone: a combination of them that cancels every
    variable but not the constant, signed to make the constant negative.
    The caller checks the sum's constant.
    """
    multipliers, total, rows = [], {}, []
    for (terms, _), coefficient, equality in zip(forms, coefficients, equalities):
        if equality:
            multipliers.append(Fraction(0))
            rows.append(len(multipliers) - 1)
            continue
        if coefficient < 0:
            return None
        multipliers.append(coefficient)
        for key, value in terms.items():
            total[key] = total.get(key, Fraction(0)) + coefficient * value
    # Gaussian elimination over the equality rows, each pivot row tracking the
    # combination of equalities it is; a later pivot row is reduced by the
    # earlier ones, so reducing the total in pivot order never reintroduces
    # an eliminated key.
    pivots = []
    for row in rows:
        terms, combination = dict(forms[row][0]), {row: Fraction(1)}
        _subtract_pivots(pivots, terms, combination)
        if not terms:
            constant = sum((value * forms[other][1] for other, value in combination.items()), Fraction(0))
            if constant:
                sign = -1 if constant > 0 else 1
                return [sign * combination.get(position, Fraction(0)) for position in range(len(forms))]
            continue
        key = min(terms)
        pivot = terms[key]
        pivots.append((key, {other: value / pivot for other, value in terms.items()},
                       {other: value / pivot for other, value in combination.items()}))
    total, combination = {key: value for key, value in total.items() if value}, {}
    _subtract_pivots(pivots, total, combination)
    if total:
        return None
    for row, value in combination.items():
        multipliers[row] = value
    return multipliers


def _subtract_pivots(pivots, terms, combination):
    """Cancel every pivot key in terms (in place), recording the subtracted rows in combination."""
    for key, pivot_terms, pivot_combination in pivots:
        factor = terms.get(key)
        if not factor:
            continue
        for other, value in pivot_terms.items():
            terms[other] = terms.get(other, Fraction(0)) - factor * value
        for other, value in pivot_combination.items():
            combination[other] = combination.get(other, Fraction(0)) - factor * value
        for other in [other for other, value in terms.items() if not value]:
            del terms[other]


def _opaque_rewrite_tactic(graph):
    """The tactic proving a theory rewrite over its atoms generalized.

    Z3's rewriter normalizes the linear atoms and the propositional
    structure around the atoms of the linear forms without using what an
    ite, a div, or an application denotes, so the rewrite holds over the
    atoms generalized once those it only renamed are bridged
    (_atom_bridge_facts): a linear goal, omega over Int and grind over
    Rat. A rewrite that does use an atom's definition ((ite c t t) to t,
    the rewriter folding a mod by its bounds) fails this attempt fast and
    is proved with the definitions unfolded, as before.
    """
    if graph.numeric == _MIXED:
        return "first | omega | grind (splits := 64)"
    return "omega" if graph.numeric == "Int" else "grind (splits := 64)"


_OPAQUE_INT_KINDS = (z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM, z3.Z3_OP_ABS, z3.Z3_OP_ITE, z3.Z3_OP_UNINTERPRETED,
                     z3.Z3_OP_TO_INT, z3.Z3_OP_SELECT, z3.Z3_OP_ARRAY_EXT,
                     z3.Z3_OP_ARRAY_DEFAULT)


def _is_opaque_int_atom(graph, node):
    """An Int term that is an atom of the linear forms (_linear_term), other than a variable."""
    return (graph.is_term(node) and graph.is_arith(node) and graph.kind(node) in _OPAQUE_INT_KINDS
            and bool(graph.arguments(node)))


def _reachable_outside(graph, formula, atoms):
    """The nodes reachable from a formula without entering the given atoms (the atoms excluded)."""
    reachable, pending = set(), [formula]
    while pending:
        node = pending.pop()
        if node in reachable or node in atoms:
            continue
        reachable.add(node)
        if not _trivial_distinct(graph, node):
            pending.extend(graph.arguments(node))
    return reachable


def _opaque_int_atoms(graph, formulas):
    """The outermost opaque Int atoms under the formulas, outer atoms first (ids are topological).

    Array terms are not entered: they stay folded in the lemmas
    (_definition_names), so a read inside a store is no atom of the goal.
    """
    atoms, pending, seen = set(), list(formulas), set()
    while pending:
        node = pending.pop()
        if node in seen:
            continue
        seen.add(node)
        if _is_opaque_int_atom(graph, node):
            atoms.add(node)
        elif not _trivial_distinct(graph, node) and not graph.is_array(node):
            pending.extend(graph.arguments(node))
    return sorted(atoms, reverse=True)


# The tactic of an euf lemma (_grind_lemma): congruence closure.
_CONGRUENCE_TACTIC = "grind (splits := 64)"


def _theory_tactic(graph):
    """The tactic proving a theory lemma, a rewrite, or an argument helper.

    Large Boolean/arithmetic rewrites can require more than grind's default
    nine case splits, even though every arithmetic atom remains linear. Over
    Int, omega (a complete decision procedure for linear integer arithmetic,
    ite over Int included, with applications of uninterpreted functions as
    atoms) goes first: grind's lia module ran out of steps on Farkas lemmas
    with several equalities and on ite splits that omega closes in well
    under a second; grind still covers goals omega does not read
    (congruences and uninterpreted atoms). Both produce kernel-checked
    proofs.

    With a product of Int terms in the certificate (_is_product), grind is
    given Int.mul_eq_zero: Z3's rewriter splits (= (* x y) 0) into (or (= x
    0) (= y 0)), which grind proves over Rat, a field, on its own but not
    over Int. (Omega takes a product of two terms as an atom, each way of
    writing it a different one; grind normalizes polynomials.)
    """
    if graph.numeric not in ("Int", _MIXED):
        return "grind (splits := 64)"
    return "first | omega | grind (splits := 64)" + (" [Int.mul_eq_zero]" if graph.integer_products else "")


def _boolean_argument_helpers(graph, reachable, atom_indices, variable_indices):
    """State excluded middle for every formula that is a Boolean argument of an application.

    Z3's egraph merges each Boolean argument with true or false as soon as
    the SAT solver assigns it, so its lemmas may rest on the two cases of an
    argument that no premise mentions, for example when preprocessing
    combined several assertions. grind splits on disjunctions in context but
    not on arbitrary propositions, so each case split is offered explicitly;
    from either case it derives _m.bool p = _m.bool True or _m.bool p = _m.bool False
    by congruence. Without arrays _folded_boolean_arguments states them
    instead, folded.
    """
    helpers = []
    for argument in _boolean_arguments(graph, reachable):
        formula = _inline(graph, argument, atom_indices, variable_indices)
        helpers.append("  have _b%d : Or (%s) (Not (%s)) := Classical.em _" % (argument, formula, formula))
    return helpers


def _boolean_arguments(graph, reachable):
    """The reachable formulas other than true and false that are arguments of an application, in id order."""
    arguments = set()
    for node in sorted(reachable):
        if graph.kind(node) == z3.Z3_OP_UNINTERPRETED:
            arguments.update(argument for argument in graph.arguments(node)
                             if not graph.is_term(argument)
                             and graph.kind(argument) not in (z3.Z3_OP_TRUE, z3.Z3_OP_FALSE))
    return sorted(arguments)


def _folded_boolean_arguments(graph, reachable):
    """The excluded-middle facts of _boolean_argument_helpers over the arguments' definitions, folded.

    Returns the have lines, their names, and the arguments, for
    _grind_lemma to revert before its unfold as it does the ite gates
    (_folded_ite_gates). Written out, an argument comparing a term over
    nested ites repeats every inner ite in full, twice (eight modular Int
    steps under a predicate: 7.3 MB of these facts in an 8.2 MB file).
    """
    lines, names, nodes = [], [], set()
    for argument in _boolean_arguments(graph, reachable):
        formula = _formula(graph, argument)
        lines.append("have _b%d : Or %s (Not %s) := Classical.em _" % (argument, formula, formula))
        names.append("_b%d" % argument)
        nodes.add(argument)
    return lines, names, nodes


def _real_argument_helpers(graph, reachable, atom_indices, variable_indices):
    """State the equality of Real or Int arguments of applications that have the same normal form.

    grind's congruence closure compares function arguments as terms and its
    linear arithmetic reasons about atoms, so (f (- x y)) and (f (+ x (* -1
    y))), which Z3's rewriter identifies, stay apart in Lean, as do (f (ite
    (> x 0) x (- x))) and (f (ite (<= x 0) (* -1 x) x)), the rewriter's
    normal form of the same ite over Real and Int alike. Every pair of
    reachable numeric arguments with one normal form (_real_argument_key)
    gets an explicit equality, which the theory tactic proves on its own
    (splitting the ite conditions) and grind then uses for congruence.
    The groups are per sort: in a qf_uflira certificate an Int and a Real
    argument may share a linear form ((ite c 1 0) and (ite c 1.0 0.0)), and
    they are injected by different maps, so no helper relates them. The
    terms that formulas floor are related the same way (_real_argument_pairs),
    also in certificates without uninterpreted symbols, and so are the
    constant indices of reads. An abs of a constant counts by its value in
    the normal form, and each equality over one is proved after the abs is
    replaced by that value (_abs_value_facts).

    Without arrays each equality is stated over the two terms' definitions,
    folded, proved after unfolding them, and then unfolded in place into
    the goal's terms; written out, an argument over nested ites repeats
    every inner ite in full (each modular step of the hard16 shape thrice,
    106 KB for six steps), and the theory tactic ran out of heartbeats on
    the elaborated statement. With arrays (whose terms the unfold keeps
    folded, see _definition_names) the statement stays written out.

    Folded, the equality is proved level by level (_argument_equality_levels):
    first the equalities of the ites of one key nested in the two terms,
    innermost first, each with only its own level unfolded and the ites
    below it folded, then the terms' own. Unfolded entirely, two arguments
    over eight nested Real ites ran the theory tactic out of heartbeats
    (2^16 branch combinations); one level is at most four. The inner
    equalities are cleared once the outer ones are proved.
    """
    helpers = []
    pairs = _real_argument_pairs(graph, reachable)

    def values(nodes):
        # The replacements of the abs terms of constants among the nodes
        # by their values, in the goal of an equality before its tactic.
        return "".join("(%s); " % line for line in _abs_value_facts(graph, nodes, atom_indices, variable_indices)[0])

    if graph.arrays:
        for first, second in pairs:
            helpers.append("  have _r%d_%d : %s = %s := by %s%s" % (
                first, second, _inline(graph, first, atom_indices, variable_indices),
                _inline(graph, second, atom_indices, variable_indices),
                values(_reachable(graph, first, second)[0]), _theory_tactic(graph)))
        return helpers
    stated, seen = [], set()
    for first, second in pairs:
        for left, right, stops in _argument_equality_levels(graph, first, second):
            if (left, right) in seen:
                continue
            seen.add((left, right))
            stated.append((left, right))
            unfolded = _reachable_outside(graph, left, stops) | _reachable_outside(graph, right, stops)
            helpers.append("  have _r%d_%d : %s = %s := by unfold %s; %s%s" % (
                left, right, _term(graph, left), _term(graph, right), " ".join(_definition_names(graph, unfolded)),
                values(unfolded), _theory_tactic(graph)))
    for first, second in pairs:
        names = " ".join(_definition_names(graph, _reachable(graph, first, second)[0]))
        helpers.append("  unfold %s at _r%d_%d" % (names, first, second))
    top = set(pairs)
    inner = ["_r%d_%d" % pair for pair in stated if pair not in top]
    if inner:
        helpers.append("  clear %s" % " ".join(inner))
    return helpers


def _argument_equality_levels(graph, first, second):
    """The equalities proving first = second level by level, innermost first: (left, right, stops) triples.

    The atoms of one level are those of the linear forms of a term, or,
    for an ite, of its condition's sides and its branches, for a to_int of
    its argument. Two terms with one key (_real_argument_key) have, per
    atom key, the same coefficients, and an atom keyed as an ite (a to_int)
    has one key with each ite (to_int) of the other term it stands for:
    those are related by equalities of their own, proved the same way,
    before the level above, which then holds over its atoms folded (stops:
    the atoms not unfolded). Two floors of one key are thus proved equal
    with only themselves unfolded, by congruence from the equality of their
    arguments (the rewriter's normal form of a to_int of a nested Real ite
    chain floors another chain). Every other atom has its
    own node as key, the same node on both sides, and stays folded too. An
    abs keyed with an ite, or ites of one key but different sorts (an Int
    ite under to_real against a Real ite), are unfolded with the level, as
    the whole terms were.
    """
    order, done, stops = [], set(), {}
    pending = [(first, second, False)]
    while pending:
        left, right, expanded = pending.pop()
        if (left, right) in done:
            continue
        if expanded:
            done.add((left, right))
            order.append((left, right, stops[(left, right)]))
            continue
        pending.append((left, right, True))
        if (left, right) in stops:
            continue
        try:
            level = _level_atoms(graph, left) | _level_atoms(graph, right)
        except ReconstructionError:
            stops[(left, right)] = set()
            continue
        groups = {}
        for atom in sorted(level):
            if graph.kind(atom) in (z3.Z3_OP_ITE, z3.Z3_OP_ABS, z3.Z3_OP_TO_INT):
                groups.setdefault(_real_atom_key(graph, atom), []).append(atom)
        # The two terms themselves are unfolded, even when one is an atom of
        # its own linear form (an application or a variable), and so is an
        # abs of a constant, which the keys count by its value.
        stop = {atom for atom in level if not _constant_abs(graph, atom)} - {left, right}
        for members in groups.values():
            if len(members) < 2:
                continue
            kinds = {graph.kind(member) for member in members}
            if kinds == {z3.Z3_OP_TO_INT} or (kinds == {z3.Z3_OP_ITE}
                                              and len({graph.decl(member).range for member in members}) == 1):
                pending.extend((one, other, False) for one, other in zip(members, members[1:]))
            else:
                # An abs, or an Int ite under to_real keyed with a Real ite:
                # no equality of their own relates them, so they are unfolded.
                stop -= set(members)
        stops[(left, right)] = stop
    return order


def _level_atoms(graph, node):
    """The atoms of a term's linear form, an abs's or to_int's argument's, an ite's condition and branches."""
    atoms = {}
    if graph.kind(node) in (z3.Z3_OP_ABS, z3.Z3_OP_TO_INT):
        _linear_term(graph, graph.arguments(node)[0], Fraction(1), atoms)
        return set(atoms)
    if graph.kind(node) != z3.Z3_OP_ITE:
        _linear_term(graph, node, Fraction(1), atoms)
        return set(atoms)
    condition, then_branch, else_branch = graph.arguments(node)
    while graph.kind(condition) == z3.Z3_OP_NOT:
        condition = graph.arguments(condition)[0]
    sides = graph.arguments(condition)
    if (graph.kind(condition) not in _ARITH_PREDICATE_NAMES and graph.kind(condition) != z3.Z3_OP_EQ) \
            or not all(graph.is_arith(side) for side in sides):
        raise ReconstructionError("ite condition is not a linear arithmetic atom")
    for term in (*sides, then_branch, else_branch):
        _linear_term(graph, term, Fraction(1), atoms)
    return set(atoms)


def _real_argument_pairs(graph, reachable):
    """The pairs of reachable numeric application arguments _real_argument_helpers relates.

    Besides the numeric arguments, the terms that reachable formulas floor
    (_floored_terms) are grouped too: the rewriter's normal form of (is_int
    t) is (= (to_real (to_int t')) t'), with t' the normal form of t,
    another node when t is a nested ite chain. Their equality, proved level
    by level, lets grind relate the two formulas (or two applications over
    them) by congruence instead of splitting both chains: six nested Real
    ites under is_int, compared directly or under a predicate, ran grind out
    of its splits.

    So are the indices of reads that are constants (_abs_free_value): the
    rewriter evaluates (select a (+ (* 2.0 0.5) (- 0.75))) to a read at 0.25,
    another node, and grind, which usually identifies the two indices on
    its own, did not in a rewrite with three more numeral expressions in
    eighths, quarters, and halves among the arguments around the read.
    """
    groups = {}
    for node in sorted(reachable):
        if graph.kind(node) == z3.Z3_OP_UNINTERPRETED:
            candidates = [argument for argument in graph.arguments(node) if graph.is_arith(argument)]
        elif graph.kind(node) == z3.Z3_OP_SELECT:
            candidates = [index for index in graph.arguments(node)[1:] if _abs_free_value(graph, index) is not None]
        elif graph.floors and not graph.is_term(node):
            candidates = _floored_terms(graph, node)
        else:
            continue
        for candidate in candidates:
            key = (graph.decl(candidate).range, _real_argument_key(graph, candidate))
            members = groups.setdefault(key, [])
            if candidate not in members:
                members.append(candidate)
    return [pair for members in groups.values() for pair in zip(members, members[1:])]


def _floored_terms(graph, formula):
    """The terms a formula floors: an is_int's argument, the arguments of the to_int atoms of a comparison's sides.

    Only terms with a linear form (_real_argument_key) are returned; the
    others are left to the theory tactic as before. The result is cached
    per node (graph.floored_terms).
    """
    cached = graph.floored_terms.get(formula)
    if cached is None:
        cached = graph.floored_terms[formula] = tuple(_uncached_floored_terms(graph, formula))
    return cached


def _uncached_floored_terms(graph, formula):
    """_floored_terms without the cache."""
    if graph.kind(formula) == z3.Z3_OP_IS_INT:
        terms = [graph.arguments(formula)[0]]
    elif (graph.kind(formula) not in _ARITH_PREDICATE_NAMES and graph.kind(formula) != z3.Z3_OP_EQ) \
            or not all(graph.is_arith(side) for side in graph.arguments(formula)):
        return []
    else:
        atoms = {}
        try:
            for side in graph.arguments(formula):
                _linear_term(graph, side, Fraction(1), atoms)
        except ReconstructionError:
            return []
        terms = [graph.arguments(atom)[0] for atom in sorted(atoms) if graph.kind(atom) == z3.Z3_OP_TO_INT]
    keyed = []
    for term in terms:
        try:
            _real_argument_key(graph, term)
        except ReconstructionError:
            continue
        keyed.append(term)
    return keyed


def _real_argument_key(graph, node):
    """The linear form of a Real or Int term, with its ite atoms keyed up to Z3's normalization.

    Variables and applications are atoms of their own; an ite whose condition
    is a linear atom is keyed by the canonical form of that condition
    (_condition_key: swapping the branches when the condition is the
    complement of the canonical atom) and by the keys of its branches. Two
    terms with one key denote the same value, which the theory tactic
    proves and the helper states. A to_int is keyed by its argument's key.
    An abs of a constant counts by its value (_constant_abs), as the
    rewriter evaluates it: (+ x (abs (- 0.25)) 0.5) has the key of (+ 0.75
    x).
    """
    cached = graph.real_keys.get(("argument", node))
    if cached is not None:
        return cached
    terms = {}
    constant = _linear_term(graph, node, Fraction(1), terms)
    for atom in [atom for atom in terms if _constant_abs(graph, atom)]:
        constant += terms.pop(atom) * _abs_free_value(graph, atom)
    atoms = [(_real_atom_key(graph, atom), value) for atom, value in terms.items() if value != 0]
    key = (tuple(sorted(atoms, key=repr)), constant)
    graph.real_keys[("argument", node)] = key
    return key


def _real_atom_key(graph, atom):
    """The key of an atom of the linear forms: an ite up to Z3's normalization, abs as its ite, else itself.

    An ite is keyed by the canonical form of its condition (_condition_key)
    and the keys of its branches, swapped when the canonical condition is
    the complement; a to_int by its argument's key. An ite whose condition
    is no linear atom, or with a branch outside the linear forms (the dead
    branch dividing by zero in the rewriter's factor cancellation, see
    _validate_graph), is opaque: its own key.

    The key of an ite, an abs, or a to_int is interned (_InternedKey, one
    per structure in a graph), so that the key of a nested chain does not
    grow with its depth: comparing, hashing, and ordering (by repr) the
    keys of the levels above stays cheap.
    """
    cached = graph.real_keys.get(("atom", atom))
    if cached is not None:
        return cached
    try:
        key = _ite_atom_key(graph, atom)
    except ReconstructionError:
        key = ("atom", atom)
    if key[0] != "atom":
        interned = graph.real_keys.get(("structure", key))
        if interned is None:
            interned = _InternedKey(key)
            interned.index = len(graph.real_keys)
            graph.real_keys[("structure", key)] = interned
        key = interned
    graph.real_keys[("atom", atom)] = key
    return key


class _InternedKey(tuple):
    """An atom key structure, one object per structure in a graph (_real_atom_key).

    Its children are interned too, so two keys denote one structure exactly
    when they are one object: equality and hashing are by identity, and
    repr is the short index the graph assigned it, deterministic since the
    keys are computed in a deterministic order. It is still the structure's
    tuple, to unpack and index.
    """

    index = 0
    __eq__ = object.__eq__
    __ne__ = object.__ne__
    __hash__ = object.__hash__

    def __repr__(self):
        return "<key %d>" % self.index


def _ite_atom_key(graph, atom):
    if graph.kind(atom) == z3.Z3_OP_ABS:
        # SMT-LIB's (abs t) is (ite (>= t 0) t (- t)), which Z3's rewriter
        # logs as (ite (<= 0 t) t (* -1 t)) with the condition normalized:
        # the key of that ite, so that the two bridge (_atom_bridge_facts)
        # instead of being split. The condition (<= 0 t) holds as 0 - t <= 0.
        argument = graph.arguments(atom)[0]
        terms = {}
        constant = _linear_term(graph, argument, Fraction(1), terms)
        condition, swapped = _condition_key(
            graph, "<=", {variable: -value for variable, value in terms.items()}, -constant)
        then_key = _real_argument_key(graph, argument)
        else_key = (tuple(sorted(((key, -value) for key, value in then_key[0]), key=repr)), -then_key[1])
    elif graph.kind(atom) == z3.Z3_OP_TO_INT:
        # The floor of a term is keyed by the term's key: the rewriter's
        # normal form of (to_int t) floors t's normal form, which may be a
        # different node (t over nested ites), and two arguments of one key
        # have one floor.
        return ("to_int", _real_argument_key(graph, graph.arguments(atom)[0]))
    else:
        if graph.kind(atom) != z3.Z3_OP_ITE:
            return ("atom", atom)
        condition, then_branch, else_branch = graph.arguments(atom)
        condition, swapped = _condition_key(graph, *_polarity_constraint(graph, condition, True))
        then_key, else_key = _real_argument_key(graph, then_branch), _real_argument_key(graph, else_branch)
    if swapped:
        then_key, else_key = else_key, then_key
    return ("ite", condition, then_key, else_key)


def _condition_key(graph, relation, terms, constant):
    """The canonical key of an ite condition that holds as sum(terms) + constant relation 0.

    Z3's rewriter normalizes the atom of a condition (0 <= 2x to 0 <= x,
    over Int 2x + 1 <= 0 to x + 1 <= 0, the rounding of _rounded) and
    writes a strict or a negated condition as the complement of a
    non-strict atom with the branches swapped (x > 0 to (ite (<= x 0) b a),
    over Int also x >= 1, its tightened form, see _polarity_constraint).
    The key is the atom with its leading coefficient positive, over Int
    primitive and rounded, choosing the complement when the leading
    coefficient is negative: over Int the complement of t <= 0 is
    -t + 1 <= 0, over Real the strict -t < 0 (keyed as the non-strict atom
    it complements), an equality has no complement and is only scaled.
    Returns the key and whether it is the complement's, in which case the
    branches of the ite are to be swapped. Two conditions with one key
    (and one swap) denote one truth value, so a wrong key costs nothing
    but a bridge the theory tactic cannot prove.
    """
    keyed = {}
    for variable, value in terms.items():
        # Two atoms with one key denote one value: one coefficient.
        key = _real_atom_key(graph, variable)
        keyed[key] = keyed.get(key, Fraction(0)) + value
    keyed = {key: value for key, value in keyed.items() if value != 0}
    swapped = False
    if relation == "<":
        # Over Real only (strict Int conditions are tightened): the strict
        # complement of the non-strict atom, branches swapped.
        relation, constant, swapped = "<=", -constant, True
        keyed = {key: -value for key, value in keyed.items()}
    if keyed:
        leading = keyed[min(keyed, key=repr)]
        if relation == "=":
            keyed = {key: value / leading for key, value in keyed.items()}
            constant /= leading
        elif graph.integer_form(terms):
            keyed, constant = _rounded(keyed, constant)
            if leading < 0:
                keyed = {key: -value for key, value in keyed.items()}
                constant, swapped = 1 - constant, not swapped
        else:
            keyed = {key: value / abs(leading) for key, value in keyed.items()}
            constant /= abs(leading)
    return (relation, tuple(sorted(keyed.items(), key=repr)), constant), swapped


def _boolean_structure(graph, node, atom_indices, memo=None, leaves=None, synthetic=None):
    """Return the propositional structure of a Boolean node over the atoms, as Lean reads it.

    The structure is a nested tuple: ("atom", index), ("true",), ("false",),
    ("not", a), ("and", a, b, ...), ("or", a, b, ...), ("implies", a, b),
    ("iff", a, b). xor, Boolean ite, distinct, and conjunctions or
    disjunctions of fewer than two arguments are expanded exactly as
    _formula_body renders them, so a proof term built over the structure
    type-checks against the unfolded definitions. A node shared by several
    parents is read once (memo); its structure object is shared, but the
    structure is still a tree, so hashing and rendering it expand the
    sharing.

    With leaves (a dict), a theory atom (an equality, a comparison, or a
    distinct over terms, or a predicate application) is the opaque leaf
    ("leaf", node, rendering), rendered by its definition name so that it is
    never unfolded, and is recorded in leaves by node; without, a theory
    atom is unsupported. A distinct over terms of which some pair has an
    equality node of its own (the alldiff literals Z3 logs) is instead the
    conjunction of its pair equalities negated, the leaves in the order
    _formula_body renders the pairs (_distinct_pair_leaves: a pair
    without a node is a synthetic leaf), so the literal (not (= a b)) of a
    clause names a conjunct of the distinct: a cnf lemma tying such a
    literal to an assertion holding the distinct (QF_UF NEQ004) was out of
    the prover's reach and unfolded the whole assertion into grind. With
    synthetic (a dict), the synthetic pair leaves are recorded there by id,
    for _leaf_bridges to tie them to the pairs written the other way.

    The nodes are read bottom up on an explicit stack, arguments left to
    right, rather than recursively: a QF_UF input asserting a conjunction
    nested a thousand levels deep exceeded Python's recursion limit.
    """
    memo = {} if memo is None else memo
    pending = [(node, False)]
    while pending:
        current, expanded = pending.pop()
        if current in memo:
            continue
        kind, arguments = graph.kind(current), graph.arguments(current)
        if expanded:
            memo[current] = _boolean_connective(kind, [memo[argument] for argument in arguments])
        elif kind == z3.Z3_OP_UNINTERPRETED and not arguments:
            memo[current] = ("atom", atom_indices[graph.nodes[current].declaration])
        elif _trivial_distinct(graph, current):
            memo[current] = ("true",)  # over a term as well as over an atom
        elif leaves is not None and arguments and (kind == z3.Z3_OP_UNINTERPRETED or graph.is_term(arguments[0])):
            pairs = _distinct_pair_leaves(graph, current, leaves)
            if pairs is None:
                memo[current] = leaves.setdefault(current, ("leaf", current, _formula(graph, current)))
            else:
                if synthetic is not None:
                    synthetic.update((pair[1], pair) for pair in pairs if pair[1] < 0)
                memo[current] = _structure_fold("and", [("not", pair) for pair in pairs])
        else:
            pending.append((current, True))
            pending.extend((argument, False) for argument in reversed(arguments))
    return memo[node]


def _distinct_pair_leaves(graph, node, leaves):
    """The leaves of a distinct's argument pairs (a = b), a before b, in rendering order, or None.

    None unless node is a distinct over terms and some pair has the node
    (= a b) or (= b a), or another distinct ranges over the same terms
    (graph.distinct_term_sets). A pair with the node (= a b) is the leaf of that
    node, recorded in leaves. A pair without one is a synthetic leaf,
    ("leaf", -(1 + a * n + b), rendering) for the n nodes of the graph (an
    id no node has, unique to the pair and an int, as the prover orders its
    splits by leaf id), rendered as _formula_body renders the conjunct
    (Not (a = b)) and not recorded in leaves; _leaf_bridges ties it by
    eq_comm to the node (= b a) or the synthetic leaf (b, a) of another
    distinct. The certificate keeps only the pairs the proof uses, so a
    wide distinct of which a few pairs are logged (thirty Int arguments,
    435 pairs, six in the proof) stayed one opaque leaf, the prover could
    not project those pairs, and the fallback unfolded every pair into
    omega and grind, which ran out of heartbeats from thirty arguments.
    Two distincts over the same terms in other orders (the rewriter
    refutes (distinct c0 ... c11) with (not (distinct c11 ... c0)) by
    sorting the arguments, and the exporter's cnf lemma ties the two) were
    two unrelated leaves, and omega over the unfolded pairs ran out of
    heartbeats from twelve Int arguments.
    """
    if graph.kind(node) != z3.Z3_OP_DISTINCT:
        return None
    arguments = graph.arguments(node)
    pairs = [(left, right, graph.equalities.get((left, right)))
             for index, left in enumerate(arguments) for right in arguments[index + 1:]]
    if all(equality is None and (right, left) not in graph.equalities for left, right, equality in pairs) \
            and graph.distinct_term_sets.get(tuple(sorted(arguments)), 0) < 2:
        return None
    return [("leaf", -(1 + left * len(graph.nodes) + right),
             "(%s = %s)" % (_term(graph, left), _term(graph, right)))
            if equality is None else leaves.setdefault(equality, ("leaf", equality, _formula(graph, equality)))
            for left, right, equality in pairs]


def _boolean_connective(kind, children):
    if kind == z3.Z3_OP_TRUE:
        return ("true",)
    if kind == z3.Z3_OP_FALSE:
        return ("false",)
    if kind == z3.Z3_OP_NOT:
        return ("not", children[0])
    if kind == z3.Z3_OP_AND:
        return _structure_fold("and", children)
    if kind == z3.Z3_OP_OR:
        return _structure_fold("or", children)
    if kind == z3.Z3_OP_IMPLIES:
        return ("implies",) + tuple(children)
    if kind in (z3.Z3_OP_EQ, z3.Z3_OP_IFF):
        return ("iff",) + tuple(children)
    if kind == z3.Z3_OP_XOR:
        if len(children) == 1:
            return children[0]  # (xor p) renders as p
        left, right = children
        return ("or", ("and", left, ("not", right)), ("and", ("not", left), right))
    if kind == z3.Z3_OP_ITE:
        condition, then_branch, else_branch = children
        return ("or", ("and", condition, then_branch), ("and", ("not", condition), else_branch))
    if kind == z3.Z3_OP_DISTINCT:
        return _structure_fold("and", [("not", ("iff", left, right))
                                       for index, left in enumerate(children) for right in children[index + 1:]])
    raise ReconstructionError("unsupported Boolean expression")


def _structure_fold(operator, children):
    """An and/or over fewer than two children renders as its unit or as the child itself."""
    if not children:
        return ("true",) if operator == "and" else ("false",)
    if len(children) == 1:
        return children[0]
    return (operator,) + tuple(children)


def _structure_children(structure):
    return structure[1:] if structure[0] in ("not", "and", "or", "implies", "iff") else ()


def _render_structure(structure):
    """Render a structure as the Lean proposition the unfolded definitions reduce to.

    Bottom up on an explicit stack (deep chains); a shared substructure is
    rendered once, by object identity, as the structures are alive throughout.
    """
    rendered = {}
    pending = [(structure, False)]
    while pending:
        current, expanded = pending.pop()
        if id(current) in rendered:
            continue
        kind = current[0]
        if kind == "atom":
            rendered[id(current)] = "(_atoms %d)" % current[1]
        elif kind == "leaf":
            rendered[id(current)] = current[2]
        elif kind in ("true", "false"):
            rendered[id(current)] = kind.capitalize()
        elif expanded:
            rendered[id(current)] = _render_connective(
                kind, [rendered[id(child)] for child in _structure_children(current)])
        else:
            pending.append((current, True))
            pending.extend((child, False) for child in _structure_children(current))
    return rendered[id(structure)]


def _render_connective(kind, children):
    """Render a connective over its rendered children as _formula_body renders the node."""
    if kind == "not":
        return "(Not %s)" % children[0]
    if kind == "and":
        return _fold("And", children, "True")
    if kind == "or":
        return _fold("Or", children, "False")
    if kind == "implies":
        return "(%s -> %s)" % tuple(children)
    return "(Iff %s %s)" % tuple(children)


def _eliminate_or(proof, handlers):
    """Apply one handler per disjunct of a right-nested disjunction proof (two or more).

    The proof is the first Or.elim's major premise, so every handler's
    binder type follows from it and the term's type is the handlers'
    common result type, with no ascription. An or structure always has two
    or more children (_structure_fold), so there are two or more handlers.
    """
    assert len(handlers) >= 2
    result = handlers[-1]
    for handler in reversed(handlers[1:-1]):
        result = "(fun _tail => Or.elim _tail %s %s)" % (handler, result)
    return "(Or.elim %s %s %s)" % (proof, handlers[0], result)


def _bullets(branches):
    """Tactic lines focusing each branch's lines (one per open goal, in order) under a bullet."""
    lines = []
    for branch in branches:
        lines.append("· " + branch[0])
        lines.extend("  " + line for line in branch[1:])
    return lines


def _reject_conjunct(position, count, proof):
    """A refutation of a right-nested conjunction of count children from a refutation of the one at position.

    mt And.left / mt And.right over the conjunct's position with the
    operands left to Lean: the `have` states the conjunction by its name
    (a definition or a let), and unification unfolds the name one level
    per step. With the operands written out, a step through a gate of n
    children was O(n) characters, and a gate whose every child is refuted
    O(n^2); a cnf lemma over a 13,000-node assertion exceeded the character
    budget that way.
    """
    term = proof
    if position < count - 1:
        term = "(mt (@And.left _ _) %s)" % term
    for _ in range(position):
        term = "(mt (@And.right _ _) %s)" % term
    return term


def _reject_disjunct(position, count, proof):
    """A refutation of the child at position from a refutation of a right-nested disjunction of count children.

    The operands follow from the refutation's type (the disjunction's name,
    unfolded one level per step), so the `have` needs no type.
    """
    term = proof
    for _ in range(position):
        term = "(mt (@Or.inr _ _) %s)" % term
    if position < count - 1:
        term = "(mt (@Or.inl _ _) %s)" % term
    return term


_PROVER_NAME = re.compile(r"\b_f\d+\b")
_PROVER_HAVE = re.compile(r"have (_f\d+)\b")


def _needed_lines(lines, rest=((), ())):
    """Drop the `have` steps of lines that neither a later line nor the rest needs.

    lines are a _PropositionalProver proof's own lines, the `have` steps
    unindented (a case analysis's branches go in rest, already bulleted);
    rest is (lines after them, the prover names those use but do not
    define). Returns the kept lines followed by rest's lines, and the
    prover names the result uses but does not define. The prover's names
    (_f followed by digits) are fresh per prover, so a name is defined once.
    """
    needed = set(rest[1])
    kept = []
    for line in reversed(lines):
        match = _PROVER_HAVE.match(line)
        if match is None:
            needed.update(_PROVER_NAME.findall(line))
        elif match.group(1) in needed:
            needed.discard(match.group(1))
            needed.update(_PROVER_NAME.findall(line, match.end()))
        else:
            continue
        kept.append(line)
    kept.reverse()
    return kept + list(rest[0]), needed


def _relevant_structures(order, facts):
    """The gates an unsat core of the facts needs, by z3 over their guarded definitions, or None.

    order is a _PropositionalProver's structures, children before parents,
    and facts are among them (held true). Every not, and, or, implies, and
    iff gate's definition is assumed under a guard of its own, the atoms and
    leaves are free, and z3 refutes the facts over the propositional
    abstraction; the gates whose guards are in the unsat core are those a
    refutation needs. The core is not minimized: on the plan-21 cnf lemma
    z3's first core (360 of 5,649 gates) was already minimal, and
    minimizing it took a hundred times the resources. z3 is an untrusted
    oracle here, as for the splits of _split_certificate: the result only
    steers the prover's search (see _PropositionalProver), whose proof Lean
    checks as any other. Returns None when z3 finds the abstraction
    satisfiable or does not decide it within _RELEVANCE_RLIMIT.
    """
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("rlimit", _RELEVANCE_RLIMIT)
    variables, guards = {}, {}
    for index, structure in enumerate(order):
        kind = structure[0]
        if kind in ("true", "false"):
            variables[structure] = z3.BoolVal(kind == "true", context)
            continue
        variables[structure] = z3.Bool("s%d" % index, context)
        if kind not in ("not", "and", "or", "implies", "iff"):
            continue  # an atom or a leaf
        children = [variables[child] for child in _structure_children(structure)]
        if kind == "not":
            body = z3.Not(children[0])
        elif kind == "and":
            body = z3.And(children)
        elif kind == "or":
            body = z3.Or(children)
        elif kind == "implies":
            body = z3.Implies(children[0], children[1])
        else:
            body = children[0] == children[1]
        guard = z3.Bool("g%d" % index, context)
        guards["g%d" % index] = (guard, structure)
        solver.add(z3.Implies(guard, variables[structure] == body))
    solver.add(*[variables[fact] for fact in facts])
    if solver.check(*[guard for guard, _ in guards.values()]) != z3.unsat:
        return None
    return {guards[str(guard)][1] for guard in solver.unsat_core()}


def _reject_disjunction(proofs):
    """A refutation of a right-nested disjunction from refutations of all its disjuncts (not_or.mpr)."""
    result = proofs[-1]
    for proof in reversed(proofs[:-1]):
        result = "(not_or.mpr (And.intro %s %s))" % (proof, result)
    return result


class _SweepLimit(Exception):
    """A sweep is beyond its limits (_SWEEP_MEMBERS, _SWEEP_CHARS): _PropositionalProver.sweep gives up."""


class _PropositionalProver:
    """Prove a propositional equivalence by a direct Lean proof, without a truth table.

    The two sides are gates over shared atoms. A direction is proved by
    assuming one side, propagating truth values through the gates (each
    propagation step is a `have` whose proof uses only the immediate
    operands, as in _gate_contradiction), and, while propagation alone does
    not settle the other side, doing case analysis on a true disjunction
    with undetermined disjuncts (Or.elim, see _case_split) or, when no
    assumed disjunction remains, splitting on an atom with Decidable.em; a
    branch ends with the other side proved or with a contradiction. Double
    negations are cancelled by Decidable.byContradiction on atoms only, so
    the proof needs no decidability instance for a compound formula, and
    only the atoms whose decidability it uses become instance parameters of
    the lemma. The proof is free of axioms. A direction not settled within
    _STRUCTURAL_REWRITE_STEPS steps or _STRUCTURAL_REWRITE_CHARS rendered
    characters, or whose splits reach a satisfying assignment (the
    equivalence does not hold), returns None and the caller falls back to
    the truth table; Lean checks the proof as it checks any other, so a
    wrong proof is rejected, never trusted.

    The proof is a tactic script (`have` steps, `refine` with one hole per
    case and a bullet each, `exact`; see _prove) and every and, or, implies
    and iff structure has a name: the caller's (`names`, the definitions of
    the nodes the structures were read from, see _structure_names) or,
    without, a tactic `let` (`_bindings`, children first). Propositions are
    stated over the names, so a step costs a few names however deep or wide
    the gates are; with the propositions written out at every step, a chain
    through a nested gate was quadratic in the gate, and the 74-way
    left-nested disjunction of a QF_LRA clock synchronization input
    exhausted the character budget after a thousand steps. A step through a
    conjunction or a disjunction names the gate and leaves its operands to
    unification (`_` under mt And.left, And.right, Or.inl, Or.inr; see
    _reject_conjunct), which unfolds the name one level: with the operands
    written out, a gate of n children cost O(n) characters per step. The
    steps whose type Lean infers from their arguments (projections,
    And.intro, mt over Or.inl and Or.inr, not_or.mpr, Or.elim over the
    disjunction's proof) carry no type.

    In classical mode (the cnf lemmas of theory certificates, see
    _cnf_lemma) the structures may hold opaque theory leaves next to the
    atoms; double negations on atoms and leaves are cancelled by
    Classical.byContradiction and splits use Classical.em, so no instance
    is needed and `needed` stays empty. Such certificates depend on the
    standard axioms through their theory lemmas anyway.

    With relevant (a set of gates, see _relevant_structures; classical mode
    only), only those gates propagate or are split as disjunctions, and the
    atom splits range over their inputs (_frontier): the search is
    restricted to the gates an unsat core of the facts needs.
    Without, every true disjunction is a candidate, the fewest open
    disjuncts first, whether or not the conflict involves it; over an
    assertion holding a disjunction per time step (QF_IDL planning
    plan-21) the search went through the cases of every earlier step before
    reaching the one the clause is about, and exhausted its budget.

    budget scales the step and character limits (see _cnf_lemma).

    With joined (a cnf lemma's leaf bridges, iff structures between a leaf
    and a leaf or its negation) and scope (the name the declarations start
    with and the arguments they are applied to), the prover relates the two
    forms of the clause's formulas gate by gate instead of searching the
    clause as a whole (sweep): classical mode, over the caller's names.
    """

    def __init__(self, *roots, classical=False, names=None, links=False, relevant=None, budget=1, joined=None,
                 scope=None):
        if (relevant is not None or joined is not None) and not classical:
            raise ValueError("a relevant set splits gates by Classical.em, so it needs classical mode")
        self.relevant = relevant
        self.inputs = (None, None)  # a relevant set and the operands of its gates (_frontier)
        self.budget = budget
        self.limits = None  # the steps and characters of one search of a sweep, in place of the budget's
        self.positions = None
        self.parents = {}
        self.order = []  # every structure, children before parents
        self.named = {}  # the and, or, implies and iff structures by their names
        self.bound = []  # the named structures bound by a tactic `let`, in order
        self.needed = set()
        self.names = set()
        self.fresh = 0
        self.steps = 0
        self.chars = 0
        self.classical = classical
        self.decidable = ("atom", "leaf") if classical else ("atom",)
        self.roots = roots
        for root in roots:
            self._index(root)
        self.linked = links
        self.links, self.representatives = (self._equivalent_structures() if links else ([], {}))
        for link in self.links:
            self._index(link)
        for structure in self.order:
            if structure[0] not in ("and", "or", "implies", "iff"):
                continue
            if names is None:
                self.named[structure] = "_s%d" % len(self.bound)
                self.bound.append(structure)
            elif structure in names:
                self.named[structure] = names[structure]
        self.scope = scope if joined is not None else None
        if joined is not None:  # a sweep, see sweep
            if names is None or scope is None:
                raise ValueError("a sweep states its links outside the proof, over the caller's names")
            self.gates, self.proved, self.failed, self.definitions = set(), {}, set(), []
            self.spent, self.allowed = 0, None  # the characters written, and how many may be (sweep)
            try:
                self.links = self._swept_structures(joined)
            except _SweepLimit:
                self.links = None  # too wide: sweep gives up
            for link in self.links or ():
                self._index(link)
        self.constants = [(structure, structure[0] == "true", "True.intro" if structure[0] == "true"
                           else "(fun _absurd => _absurd)")
                          for structure in (("true",), ("false",)) if structure in self.parents]
        self._tautologies = None  # see tautologies
        self.stated = frozenset()  # those of them that are facts of the proof under way

    @property
    def tautologies(self):
        """The excluded-middle facts (_excluded_middles), found when the first implication asks for them.

        A prover that only refutes (the cnf lemmas, a dozen provers over a
        400-operand assertion each in QF_UF NEQ004) never states them, so it
        does not render them either.
        """
        if self._tautologies is None:
            self._tautologies = self._excluded_middles() if self.classical else []
        return self._tautologies

    def _excluded_middles(self):
        """The disjunctions holding a disjunct and its negation, each true by excluded middle, with the proof.

        A fact of every implication proved (_implication). Nothing
        propagates into such a disjunction before one of its disjuncts has
        a value, so the search split on an atom or leaf for each one it
        met, both branches going on to the next: Z3's rewriter drops the
        clauses (or (not A) A) of a conjunction, and proving the
        conjunction with them from the one without took 2^k cases for k
        of them (each of the five 25-clause conjunctions of a QF_UF
        quasigroup input has five; from seven on the search gave up). The
        case analysis of such a proof skips these disjunctions (_case_split).
        A refutation (the cnf lemmas) is searched as before, without them.
        """
        found = []
        for structure in self.order:
            if structure[0] != "or":
                continue
            children = _structure_children(structure)
            positions = {child: position for position, child in reversed(list(enumerate(children)))}
            for negative, child in enumerate(children):
                if child[0] == "not" and child[1] in positions:
                    found.append((structure, True, "(Or.elim (Classical.em %s) (fun _g => %s) (fun _g => %s))" % (
                        self._render(child[1]), _inject(positions[child[1]], len(children), "_g"),
                        _inject(negative, len(children), "_g"))))
                    break
        return found

    def _index(self, root):
        """Index root's structures depth first, children before parents, on an explicit stack (deep chains)."""
        if root in self.parents:
            return
        self.parents[root] = {}
        stack = [(root, iter(_structure_children(root)))]
        while stack:
            structure, children = stack[-1]
            child = next(children, None)
            if child is None:
                stack.pop()
                self.order.append(structure)
                if stack:
                    self.parents[structure][stack[-1][0]] = None
            elif child in self.parents:
                self.parents[child][structure] = None
            else:
                self.parents[child] = {}
                stack.append((child, iter(_structure_children(child))))

    def _render(self, structure):
        """Render a structure inside the proof: a named one by its name, the rest one level over the names."""
        if structure in self.named:
            return self.named[structure]
        return self._shallow(structure)

    def _shallow(self, structure):
        if structure[0] not in ("not", "and", "or", "implies", "iff"):
            return _render_structure(structure)
        return _render_connective(structure[0], [self._render(child) for child in _structure_children(structure)])

    def _bindings(self):
        """The tactic `let` lines binding the structures this prover named itself, children first."""
        return ["let %s : Prop := %s" % (self.named[structure], self._shallow(structure)) for structure in self.bound]

    def name(self):
        """A fresh hypothesis name, reused rather than restated when it appears as a proof."""
        self.fresh += 1
        self.names.add("_f%d" % self.fresh)
        return "_f%d" % self.fresh

    def _relevant(self, structure):
        """Whether the search may use the gate structure (always without a relevant set)."""
        return self.relevant is None or structure in self.relevant

    def _frontier(self, state):
        """The undetermined inputs of the relevant gates as sort keys and structures, most read first.

        An input is an atom, a leaf, or a gate outside the relevant set: the
        unsat core does not need its definition, so it does not propagate
        and is split like an atom (Classical.em on its name), or a
        refutation that holds whatever its value would end with it
        undetermined.
        """
        if self.inputs[0] is not self.relevant:
            # The operands of the relevant gates, once per relevant set: a
            # search over a few gates of a large clause (sweep) must not walk
            # the clause at every split.
            self.inputs = (self.relevant, {child for gate in self.relevant for child in _structure_children(gate)})
        positions = self._positions()
        return sorted((-len(self.parents[structure]), positions[structure], structure)
                      for structure in self.inputs[1]
                      if structure not in state and structure[0] not in ("true", "false")
                      and (structure[0] in self.decidable or structure not in self.relevant))

    def _positions(self):
        """The index of every structure in the order, those indexed since the last call included."""
        if self.positions is None:
            self.positions = {}
        for position in range(len(self.positions), len(self.order)):
            self.positions[self.order[position]] = position
        return self.positions

    def _exhausted(self):
        steps, chars = self.limits or (_STRUCTURAL_REWRITE_STEPS * self.budget,
                                       _STRUCTURAL_REWRITE_CHARS * self.budget)
        return self.steps > steps or self.chars > chars

    def equivalence(self, left, right):
        """Tactic lines proving the goal Iff left right (as Lean reads the two structures), or None."""
        links, facts = self._prove_links()
        forward = self._implication(left, right, facts)
        backward = self._implication(right, left, facts) if forward is not None else None
        if backward is None:
            return None
        return self._bindings() + links + ["refine Iff.intro (fun (%s : %s) => ?_) (fun (%s : %s) => ?_)" % (
            forward[0], self._render(left), backward[0], self._render(right))] + _bullets([forward[1], backward[1]])

    def _equivalent_structures(self):
        """The links (iff structures) between structures equal up to flattening, order, and double negation.

        A structure's class is its and/or flattened into the set of its
        operands' classes (duplicates dropped, a single operand standing for
        itself), its double negation the class of the negated structure, and
        an iff the set of its sides' classes. Each structure is linked to
        the first of its class, children before parents. The rewriter
        flattens, sorts, and deduplicates the gates over the normalized
        atoms, so the two sides of a rewrite are mostly such structures: the
        search alone splits every disjunction it assumes, and the case
        splits of the disjunctions of one conjunction multiply (the spider
        QF_LRA rewrites exhausted the character budget that way). Proved
        children first (_prove_links), each link is a fact of the next
        ones and of the search, and a disjunction case closes as soon as it
        reaches a linked operand.
        """
        classes, keys, interned, representatives, links = {}, [], {}, {}, []
        # The roots each structure is under: two structures under one root
        # only (prefixes of one left-nested chain that differ by a repeated
        # disjunct) are not linked, as the search would walk the chain once
        # per link; the search relates them through the other side's links.
        sides = {}
        for position, root in enumerate(self.roots):
            for structure in self._descendants(root):
                sides[structure] = sides.get(structure, frozenset()) | {position}

        def intern(key):
            if key not in interned:
                interned[key] = len(keys)
                keys.append(key)
            return interned[key]

        true, false = intern(("true",)), intern(("false",))
        for structure in self.order:
            kind = structure[0]
            children = [classes[child] for child in _structure_children(structure)]
            if kind == "not" and keys[children[0]][0] == "not":
                cls = keys[children[0]][1]
            elif kind == "not":
                cls = {true: false, false: true}.get(children[0], None)
                if cls is None:
                    cls = intern(("not", children[0]))
            elif kind in ("and", "or"):
                unit, zero = (true, false) if kind == "and" else (false, true)
                members = set()
                for child in children:
                    members |= keys[child][1] if keys[child][0] == kind else {child}
                members.discard(unit)
                if zero in members or not members:
                    cls = zero if members else unit
                elif len(members) == 1:
                    cls = next(iter(members))
                else:
                    cls = intern((kind, frozenset(members)))
            elif kind == "iff":
                cls = intern(("iff", frozenset(children)))
            elif kind == "implies":
                cls = intern(("implies", tuple(children)))
            else:
                cls = intern(structure)
            classes[structure] = cls
            representative = representatives.setdefault(cls, structure)
            if representative != structure and (sides[structure] != sides[representative]
                                                or len(sides[structure]) > 1):
                links.append(("iff", structure, representative))
        return links, {structure: representatives[cls] for structure, cls in classes.items()}

    def _prove_links(self):
        """The `have` lines proving the links, and the facts they give, children first.

        An iff linked to an iff is proved by iff_congr from its sides'
        links; any other link by the search in both directions, from the
        links below it. A link not proved within the budget is dropped and
        its steps and characters given back.

        The links have an allowance of _LINK_STEPS and _LINK_CHARS each on
        top of the budget, in total at most the budget's own steps and
        characters, and the allowance they leave is not carried over
        to the search over the sides: it starts where it would have without
        it, or after the steps and characters the links took beyond it.
        """
        start = self.steps, self.chars
        self.steps -= min(len(self.links) * _LINK_STEPS, _STRUCTURAL_REWRITE_STEPS * self.budget)
        self.chars -= min(len(self.links) * _LINK_CHARS, _STRUCTURAL_REWRITE_CHARS * self.budget)
        lines, facts, proofs = [], [], {}

        def equivalent(structure, other):
            """A proof of structure <-> other from the proved links, or None."""
            if structure == other:
                return "Iff.rfl"
            if self.representatives[structure] != self.representatives[other]:
                return None
            ends = []
            for end in (structure, other):
                representative = self.representatives[end]
                ends.append("Iff.rfl" if end == representative else proofs.get(("iff", end, representative)))
            if None in ends:
                return None
            return "(Iff.trans %s (Iff.symm %s))" % tuple(ends)

        for link in self.links:
            _, structure, representative = link
            relevant = self._descendants(structure) | self._descendants(representative)
            if structure[0] == "iff" and representative[0] == "iff":
                (a, b), (c, d) = structure[1:], representative[1:]
                straight = [equivalent(a, c), equivalent(b, d)]
                crossed = [equivalent(a, d), equivalent(b, c)]
                if None not in straight:
                    proof = "(iff_congr %s %s)" % tuple(straight)
                elif None not in crossed:
                    proof = "(Iff.trans (iff_congr %s %s) iff_comm)" % tuple(crossed)
                else:
                    continue
                proof_lines = None
            else:
                steps, chars = self.steps, self.chars
                below = [fact for fact in facts if fact[0][1] in relevant]
                forward = self._implication(structure, representative, below)
                backward = self._implication(representative, structure, below) if forward is not None else None
                if backward is None:
                    self.steps, self.chars = steps, chars
                    continue
                proof_lines = ["refine Iff.intro (fun (%s : %s) => ?_) (fun (%s : %s) => ?_)" % (
                    forward[0], self._render(structure), backward[0], self._render(representative))]
                proof_lines += _bullets([forward[1], backward[1]])
            name = self.name()
            if proof_lines is None:
                line = "have %s : %s := %s" % (name, self._render(link), proof)
                lines.append(line)
                self.chars += len(line)
            else:
                lines.append("have %s : %s := by" % (name, self._render(link)))
                self.chars += len(lines[-1])
                lines.extend("  " + line for line in proof_lines)
            proofs[link] = name
            facts.append((link, True, name))
        self.steps, self.chars = max(self.steps, start[0]), max(self.chars, start[1])
        return lines, facts

    def _swept_structures(self, joined):
        """The classes of the structures and the links a sweep starts from, children first.

        A class is what Z3's rewriter makes of a structure before it logs
        the clauses of a formula, as far as that is read here:

        - the leaves that joined ties (a cnf lemma's leaf bridges: iff
          structures between a leaf and a leaf or its negation) share a
          class or have complementary ones;
        - an and/or is the set of its operands' classes, flattened, without
          units, and false (true) when it holds a member and its negation;
        - a negation is its operand's class negated, cancelling a double
          negation, an implication the disjunction it is rewritten to, and
          an iff is keyed by its sides without their negations (one with a
          constant side is the other side or its negation);
        - a Boolean ite, read (or (and c t) (and (not c) e)), follows the
          rewriter's mk_ite_core: (ite c false e) is (and (not c) e),
          (ite c true e) is (or c e), (ite c t (not t)) is (= c t), and so
          on; any other ite is the or of its two guarded branches.

        The representative of a class is its first structure, or the
        negation of the first structure of the complementary class. A
        structure the caller named (a node's definition) is linked to its
        class's representative unless it is that; a named structure whose
        class is flattened into the class of some gate is linked to the
        class's canonical gate instead, as is every other of its class:
        the and/or of the members' representatives in the order of the
        classes, where two structures that group the operands of one
        conjunction differently meet (_canonical). Negations, atoms,
        leaves, and the unnamed gates (the two branches of an ite) are
        never linked: a search reads through them. The classes only
        propose the links; each is proved or dropped (sweep).
        """
        self.group = {}  # a joined leaf: the leaf it is tied to, and whether as its negation
        for _, left, right in joined:
            negated = right[0] == "not"
            right = right[1] if negated else right
            for leaf in (left, right):
                self.group.setdefault(leaf, (leaf, False))
            (root, sign), (other, other_sign) = self._find(left), self._find(right)
            if root != other:
                self.group[other] = (root, sign ^ other_sign ^ negated)
        keys, interned, flattened = [], {}, set()
        self.classes, self.keys, self.representatives, self.canonical = {}, keys, {}, {}
        self.members = 0  # of the and/or classes, within _SWEEP_MEMBERS

        def intern(key):
            if key not in interned:
                interned[key] = len(keys)
                keys.append(key)
            return interned[key]

        true, false = intern(("true",)), intern(("false",))
        self.representatives[true], self.representatives[false] = (("true",), False), (("false",), False)

        def negate(cls):
            if cls in (true, false):
                return true + false - cls
            return keys[cls][1] if keys[cls][0] == "not" else intern(("not", cls))

        def gate(kind, operands):
            unit, zero = (true, false) if kind == "and" else (false, true)
            members = set()
            for operand in operands:
                if keys[operand][0] == kind:
                    flattened.add(operand)
                    members |= keys[operand][1]
                else:
                    members.add(operand)
            members.discard(unit)
            if zero in members or any(keys[member][0] == "not" and keys[member][1] in members for member in members):
                return zero
            if len(members) < 2:
                return next(iter(members)) if members else unit
            key = (kind, frozenset(members))
            if key not in interned:
                self.members += len(members)
                if self.members > _SWEEP_MEMBERS:
                    raise _SweepLimit()
            return intern(key)

        def iff(left, right):
            sides = [keys[side][1] if keys[side][0] == "not" else side for side in (left, right)]
            negated = (sides[0] != left) != (sides[1] != right)
            if sides[0] == sides[1]:
                cls = true
            elif sides[0] in (true, false) or sides[1] in (true, false):
                constant, other = sides if sides[0] in (true, false) else reversed(sides)
                cls = other if constant == true else negate(other)
            else:
                cls = intern(("iff", frozenset(sides)))
            return negate(cls) if negated else cls

        def ite(condition, then, other):
            if condition in (true, false) or then == other:
                return then if condition != false else other
            if then in (true, false):
                return gate("or", [condition, other]) if then == true else gate("and", [negate(condition), other])
            if other in (true, false):
                return gate("or", [negate(condition), then]) if other == true else gate("and", [condition, then])
            if condition == other:
                return gate("and", [condition, then])
            if condition == then:
                return gate("or", [condition, other])
            if then == negate(other):
                return iff(condition, then)
            return gate("or", [gate("and", [condition, then]), gate("and", [negate(condition), other])])

        for structure in self.order:
            kind = structure[0]
            operands = [self.classes[child] for child in _structure_children(structure)]
            if structure in self.group:
                leaf, negated = self._find(structure)
                cls = negate(intern(leaf)) if negated else intern(leaf)
            elif kind == "not":
                cls = negate(operands[0])
            elif (kind == "or" and len(structure) == 3 and structure[1][0] == structure[2][0] == "and"
                  and len(structure[1]) == len(structure[2]) == 3 and structure[2][1] == ("not", structure[1][1])):
                # A Boolean ite as _boolean_connective reads it.
                cls = ite(self.classes[structure[1][1]], self.classes[structure[1][2]], self.classes[structure[2][2]])
            elif kind in ("and", "or"):
                cls = gate(kind, operands)
            elif kind == "implies":
                cls = gate("or", [negate(operands[0]), operands[1]])
            elif kind == "iff":
                cls = iff(*operands)
            else:
                cls = intern(structure)
            self.classes[structure] = cls
            if kind != "not":
                negated = keys[cls][0] == "not"
                self.representatives.setdefault(keys[cls][1] if negated else cls, (structure, negated))
        links = []
        for structure in self.order:
            if structure[0] in ("not", "atom", "leaf", "true", "false"):
                continue
            cls = self.classes[structure]
            base = keys[cls][1] if keys[cls][0] == "not" else cls
            if structure not in self.named and (base not in flattened
                                                 or self.representatives[base][0] is not structure):
                continue  # read through, unless it stands for a class that is flattened
            target = self._canonical(structure) if base in flattened else self._literal(cls)
            if target != structure:
                links.append(("iff", structure, target))
        return links

    def _literal(self, cls):
        """The representative of a class: its first structure, or the negation of the complementary class's."""
        negated = self.keys[cls][0] == "not"
        representative, sign = self.representatives[self.keys[cls][1] if negated else cls]
        return representative if sign == negated else ("not", representative)

    def _canonical(self, structure):
        """The canonical gate of a structure's and/or class (negated for the complementary class), or None."""
        cls = self.classes[structure]
        negated = self.keys[cls][0] == "not"
        base = self.keys[cls][1] if negated else cls
        if self.keys[base][0] not in ("and", "or"):
            return None
        if base not in self.canonical:
            gate = self.canonical[base] = (self.keys[base][0],) + tuple(
                self._literal(member) for member in sorted(self.keys[base][1]))
            self.gates.add(gate)
            if gate not in self.named:
                # Named by a definition of its own, as the nodes' gates are:
                # a step states it by that name however wide it is.
                self.definitions.append(("%s_k%d" % (self.scope[0], len(self.definitions)), self._shallow(gate)))
                self.spent += len(self.definitions[-1][1])
                self.named[gate] = "(%s%s)" % (self.definitions[-1][0], self.scope[1])
        return ("not", self.canonical[base]) if negated else self.canonical[base]

    def _find(self, leaf):
        """The leaf a joined leaf is tied to through the joining facts, and whether as its negation."""
        root, negated = self.group[leaf]
        while self.group[root][0] != root:
            root, sign = self.group[root]
            negated ^= sign
        return root, negated

    @staticmethod
    def _end(link):
        """The structure a link ties its structure to, without the negation."""
        return link[2][1] if link[2][0] == "not" else link[2]

    def _local(self, roots, rounds):
        """The gates from roots down to the named structures, the facts that tie those, and the untied ones.

        The search of a link's proof, and of the refutation after the
        sweep, is restricted to these gates (`relevant`). Below a named
        structure nothing is read: its link's fact stands for it, and
        without one it is an input, as an atom is (unless its link was
        tried and not proved: then it is read through). A fact ties the
        structure to a representative, whose own fact is taken with it, or
        to a canonical gate. A canonical gate propagates between its
        operands, which are not walked either: the operands of the gates
        met are tied by their facts in turn, rounds times. The facts are
        these links, the joining facts of the joined leaves met, and the
        constants met; the untied structures are the named ones met
        without a fact.
        """
        gates, facts, groups, opened, untied = set(), {}, set(), {}, []
        seen = set(roots)

        def walk(pending, depth):
            while pending:
                structure = pending.pop()
                if structure in self.gates:
                    opened.setdefault(structure, depth)
                elif structure not in roots and structure in self.proved:
                    facts[structure] = self.proved[structure]
                    end = self._end(facts[structure][0])
                    if end not in seen:
                        # A representative stands for its class: it is not read.
                        seen.add(end)
                        if end in self.gates or end in self.proved:
                            pending.append(end)
                        elif end in self.named and end not in self.failed:
                            untied.append(end)
                elif structure not in roots and structure in self.named and structure not in self.failed:
                    untied.append(structure)
                else:
                    if structure in self.group:
                        groups.add(self._find(structure)[0])
                    children = _structure_children(structure)
                    if children:
                        gates.add(structure)
                    for child in children:
                        if child not in seen:
                            seen.add(child)
                            pending.append(child)

        walk(list(roots), 0)
        for depth in range(rounds):
            for gate in [gate for gate, level in opened.items() if level == depth]:
                operands = [operand for operand in gate[1:] if operand not in seen]
                seen.update(operands)
                walk(operands, depth + 1)
        for gate in opened:
            gates.add(gate)
            gates.update(operand for operand in gate[1:] if operand[0] == "not")
            seen.update(gate[1:])
        facts = list(facts.values())
        facts.extend(fact for group in sorted(groups, key=self._positions().get) for fact in self.joins[group])
        for fact in facts:  # the facts propagate as gates, and so do the negations they tie
            gates.add(fact[0])
            gates.update(side for side in fact[0][1:] if side[0] == "not")
        return gates, facts + [constant for constant in self.constants if constant[0] in seen], untied

    def _tie(self, link, blocks):
        """Prove a link over its local gates and record its fact and its theorem, or return the untied structures."""
        _, left, right = link
        for rounds in _SWEEP_ROUNDS:
            self.relevant, below, untied = self._local((left, self._end(link)), rounds)
            self.relevant.add(right)
            directions = []
            for source, target in ((left, right), (right, left)):
                self.steps, self.chars = 0, 0
                hypothesis, negation = self.name(), self.name()
                lines = self._prove(dict(), ("false",),
                                    below + [(source, True, hypothesis), (target, False, negation)])
                if lines is None:
                    self._spend(self.chars)  # what the search wrote before it gave up
                    break
                directions.append([hypothesis, "refine Classical.byContradiction (fun %s => ?_)" % negation] + lines)
            if len(directions) == 2:
                break
        else:
            return untied
        name = "%s_s%d" % (self.scope[0], len(blocks))
        lines = ["refine Iff.intro (fun %s => ?_) (fun %s => ?_)" % (directions[0][0], directions[1][0])]
        blocks.append((name, self._render(link), lines + _bullets([direction[1:] for direction in directions])))
        self._spend(len(blocks[-1][1]) + sum(len(line) + 1 for line in blocks[-1][2]))
        fact = "(%s%s)" % (name, self.scope[1])
        self.names.add(fact)
        self.proved[left] = (link, True, fact)
        return None

    def _spend(self, chars):
        """Count characters a sweep wrote against what it may write (sweep); _SweepLimit beyond that."""
        self.spent += chars
        if self.spent > self.allowed:
            raise _SweepLimit()

    def _open(self, untied, blocks):
        """Tie the untied structures of and/or classes to their canonical gates; whether any was."""
        tied = False
        for structure in untied:
            target = None if structure in self.proved or structure in self.failed else self._canonical(structure)
            if target is None:
                continue
            if target == structure:
                tied = True  # its own canonical gate, known as one from here on
                continue
            link = ("iff", structure, target)
            self._index(link)
            if self._tie(link, blocks) is None:
                tied = True
            else:
                self.failed.add(structure)
        return tied

    def sweep(self, structure, facts, chars=None):
        """Tactic lines proving the goal Not structure under the named facts through the links, or None.

        The plain search (refutation) relates a clause Z3 logged over its
        rewriter's form of an assertion to the assertion itself only by
        case splits on the atoms and leaves the two forms share: over two
        forms of one circuit (QF_IDL RTCL ckt_PROP1_tf_20: twenty frames of
        Boolean ite chains, 4,000 gates each way, 77 pairs of bridged
        leaves) it splits without end, with or without z3's unsat core.
        Here the two forms are swept bottom up, as an equivalence checker
        sweeps two circuits: the named structures are linked to the
        representatives or canonical gates of their classes
        (_swept_structures), and each link is proved, children first, by a
        search over the few gates between its two ends and the links below
        them (_local), within _SWEEP_LINK_STEPS steps and _SWEEP_LINK_CHARS
        characters. When that search fails, the named structures it met
        without a fact are tied to their canonical gates (_open) and it is
        repeated once; a link still not proved is dropped, and the gates
        under its structure are read by the links above. The clause is then
        refuted over the gates above the links, opening what it meets up to
        _SWEEP_OPENINGS times. facts are the joining facts (see __init__)
        with their proofs. Returns the declarations the refutation needs
        and its tactic lines: a canonical gate as (name, None, [body]), a
        link as (name, statement, tactic lines), the gates first and the
        links in the order they were proved. A link is a theorem of its
        own and a fact by its name applied to the scope's arguments, where
        a `have` would count its proof against the heartbeats of the
        lemma. The sweep is bounded as a whole, where a link's search is
        bounded by itself: it gives up when the and/or classes have more
        than _SWEEP_MEMBERS members (_swept_structures), and as soon as the
        canonical gates, the links proved, and the searches that failed
        have written more than chars characters (_SWEEP_CHARS by default),
        so that a formula it does not fit (a thousand nested conjunctions)
        costs seconds and the lemma keeps its other proofs.
        """
        if self.links is None:
            return None
        self.allowed = _SWEEP_CHARS if chars is None else chars
        try:
            return self._swept(structure, facts)
        except _SweepLimit:
            return None

    def _swept(self, structure, facts):
        """The declarations and the refutation of a sweep within its limits (sweep)."""
        self.joins = {}  # the joining facts by the leaf their leaves are tied to
        for fact, name in facts:
            self.joins.setdefault(self._find(fact[1])[0], []).append((fact, True, name))
        self.names.update(name for _, name in facts)
        blocks = []
        self.limits = (_SWEEP_LINK_STEPS, _SWEEP_LINK_CHARS)
        for link in self.links:
            untied = self._tie(link, blocks)
            if untied is not None and not (self._open(untied, blocks) and self._tie(link, blocks) is None):
                self.failed.add(link[1])
        refutation = None
        for _ in range(_SWEEP_OPENINGS):
            self.relevant, below, untied = self._local((structure, structure[1]), _SWEEP_ROUNDS[-1])
            self.limits = None
            self.steps, self.chars = 0, 0
            refutation = self.refutation(structure, [(fact, name) for fact, truth, name in below
                                                     if _structure_children(fact)])
            self.limits = (_SWEEP_LINK_STEPS, _SWEEP_LINK_CHARS)
            if refutation is not None or not self._open(untied, blocks):
                break
        if refutation is None:
            return None
        # The links the refutation uses, those their proofs use, and the
        # canonical gates all of them state.
        stated = re.compile(r"\b%s_[ks]\d+\b" % re.escape(self.scope[0]))
        needed, kept = set(stated.findall("\n".join(refutation))), []
        for name, statement, lines in reversed(blocks):
            if name in needed:
                needed.update(stated.findall(statement + "\n".join(lines)))
                kept.append((name, statement, lines))
        for name, body in reversed(self.definitions):
            if name in needed:
                needed.update(stated.findall(body))
                kept.append((name, None, [body]))
        return kept[::-1], refutation

    def _descendants(self, root):
        """The structures under root, root included."""
        seen, pending = set(), [root]
        while pending:
            structure = pending.pop()
            if structure not in seen:
                seen.add(structure)
                pending.extend(_structure_children(structure))
        return seen

    def implication(self, source, target):
        """Tactic lines proving the goal source -> target, or None."""
        result = self._implication(source, target)
        if result is None:
            return None
        hypothesis, lines = result
        return self._bindings() + ["refine (fun (%s : %s) => ?_)" % (hypothesis, self._render(source))] + lines

    def _implication(self, source, target, facts=()):
        """The hypothesis name and the tactic lines proving target under it and the facts, or None.

        With links (classical), the target's negation is assumed too and
        the lines refute both: a false disjunction makes all its disjuncts
        false at once, where proving one up a left-nested chain of n
        disjunctions takes n steps in each of n cases (the 250-way
        disjunction of the clock synchronization QF_LRA rewrite, flattened
        on the other side, exceeded the character budget that way).
        """
        hypothesis = self.name()
        constants = self.constants
        if self.tautologies:
            # Those under the two sides: a link is proved from what is below it.
            below = self._descendants(source) | self._descendants(target)
            stated = [fact for fact in self.tautologies if fact[0] in below]
            constants = constants + stated
            self.stated = frozenset(fact[0] for fact in stated)
        if self.linked:
            negation = self.name()
            lines = self._prove(dict(), ("false",), constants + list(facts)
                                + [(source, True, hypothesis), (target, False, negation)])
            if lines is None:
                return None
            return hypothesis, ["refine Classical.byContradiction (fun (%s : Not %s) => ?_)" % (
                negation, self._render(target))] + lines
        lines = self._prove(dict(), target, constants + list(facts) + [(source, True, hypothesis)])
        if lines is None:
            return None
        return hypothesis, lines

    def refutation(self, structure, facts=()):
        """Tactic lines proving the goal Not structure under the named facts (hypotheses in scope), or None."""
        hypothesis = self.name()
        self.stated = frozenset()
        self.names.update(name for _, name in facts)
        lines = self._prove(dict(), ("false",), self.constants + [(fact, True, name) for fact, name in facts]
                            + [(structure, True, hypothesis)])
        if lines is None:
            return None
        return self._bindings() + ["refine (fun (%s : %s) => ?_)" % (hypothesis, self._render(structure))] + lines

    def _negatable(self, structure):
        """Whether a double negation of structure can be cancelled: any structure classically, else an atom."""
        return self.classical or structure[0] == "atom"

    def _by_contradiction(self, structure, body):
        """A proof of structure from body, a proof of False under _g : Not structure; the atom it decides."""
        if self.classical:
            return "(Classical.byContradiction (fun _g => %s))" % body, None
        return "(Decidable.byContradiction (fun _g => %s))" % body, structure[1]

    def _prove(self, state, target, facts):
        """Tactic lines proving the goal target under the state extended by the facts, or None.

        The lines are `have` steps, then `exact` the target's proof or a
        case analysis: `refine` over Or.elim with one hole per case and a
        bullet per hole, in order. Written as tactics rather than as one
        nested term because Lean elaborates a term of nested `have`s in time
        quadratic in their number (every binder abstracts the whole rest of
        the term; 1,000 steps took nine minutes as a term and five seconds
        as tactics), and a cnf lemma over a 13,000-node assertion has
        ten thousand steps.

        The case analyses nest on an explicit stack of open splits, each
        branch proved in order and closed into its split's lines once its
        last branch is, rather than by recursion: a search through a
        thousand nested splits (the cnf lemma of a QF_LRA time-triggered
        startup input, tta_startup simple_startup_11nodes) exceeded Python's
        recursion limit. Lean checks a thousand nested bullets in a second.

        A proved branch keeps only the `have` steps its proof needs
        (_needed_lines), and a branch whose proof does not need its
        hypothesis proves the goal before the split, which is dropped with
        its other branches (backjumping). Propagation writes a step for every
        consequence, most of them unused, and the atom splits are taken
        most-shared first, irrespective of the conflict: the cnf lemma of a
        QF_IDL circuit (RTCL ckt_PROP1_tf_10, 97 leaves) split 31 atoms deep
        and exhausted the character budget enumerating splits whose both
        branches closed by facts found before them.
        """
        splits = []  # open splits: (lines, branch facts, state, header, names, branches)
        result = self._settle(state, target, facts)
        while True:
            if isinstance(result, tuple):  # a split: prove its first branch
                splits.append(result)
            elif result is None:
                return None  # a branch not proved fails the whole proof
            else:
                proof = _needed_lines(result)  # (lines, the names they use but do not define)
                while splits:
                    lines, branch_facts, state, header, names, branches = splits[-1]
                    if names[len(branches)] not in proof[1]:
                        splits.pop()  # backjump: the branch holds without its hypothesis
                        proof = _needed_lines(lines, proof)
                        continue
                    branches.append(proof)
                    if len(branches) < len(branch_facts):
                        break
                    splits.pop()
                    used = set().union(*(branch[1] for branch in branches))
                    proof = _needed_lines(lines + [header(names)],
                                          (_bullets([branch[0] for branch in branches]), used))
                    proof = proof[0], proof[1] - set(names)  # the header binds the branches' hypotheses
                if not splits:
                    return proof[0]
            lines, branch_facts, state, header, names, branches = splits[-1]
            structure, truth = branch_facts[len(branches)]
            names.append(self.name())
            result = self._settle(dict(state), target, [(structure, truth, names[-1])])

    def _settle(self, state, target, facts):
        """Tactic lines closing the goal by propagation alone, None, or the split to prove it by.

        A split is (lines, branch facts, state, header, names, branches): the
        lines before it, one (structure, truth) per branch, the state the
        branches extend, the function from the branches' hypothesis names to
        the `refine` line, and the names and branch lines proved so far.
        """
        lines, pending = [], []
        conflict = None
        for structure, truth, proof in facts:
            conflict = conflict or self._assign(state, lines, pending, structure, truth, proof)
        conflict = conflict or self._propagate(state, lines, pending)
        if conflict is not None:
            return lines + ["exact (False.elim %s)" % conflict]
        if target in state and state[target][0]:
            return lines + ["exact %s" % state[target][1]]
        self.steps += 1
        if self._exhausted():
            return None
        disjunction = self._case_split(state)
        if disjunction is not None:
            structure, proof = disjunction

            def header(names):
                return "refine " + _eliminate_or(proof, ["(fun %s => ?_)" % name for name in names])
            return lines, [(child, True) for child in _structure_children(structure)], state, header, [], []
        if self.relevant is None:
            atoms = sorted((-len(self.parents[atom]), atom[1], atom) for atom in self.parents
                           if atom[0] in self.decidable and atom not in state)
        else:
            atoms = self._frontier(state)
        if not atoms:
            return None  # every atom assigned without the target holding: the equivalence does not hold
        atom = atoms[0][2]
        if self.classical:
            split = "(Classical.em %s)" % self._render(atom)
        else:
            self.needed.add(atom[1])
            split = "(Decidable.em (_atoms %d))" % atom[1]

        def header(names):
            return "refine (Or.elim %s (fun %s => ?_) (fun %s => ?_))" % (split, names[0], names[1])
        return lines, [(atom, True), (atom, False)], state, header, [], []

    def _case_split(self, state):
        """A true disjunction with two or more undetermined disjuncts and no true one, with its proof, or None.

        Its disjuncts are the cases (Or.elim); each adds one fact and a
        disjunction of n cases is proved in n branches, where splitting on
        the atoms it shares with other gates could branch on every atom
        before a case closes (a 74-way disjunction exhausted the step budget
        that way). The disjunction with the fewest undetermined disjuncts
        comes first, then the earliest indexed.
        """
        best = None
        if self.relevant is None:
            candidates = enumerate(self.order)
        else:
            positions = self._positions()
            candidates = ((positions[structure], structure) for structure in self.relevant)
        for position, structure in candidates:
            value = state.get(structure)
            if structure[0] != "or" or value is None or not value[0] or not self._relevant(structure):
                continue
            if structure in self.stated:
                continue  # true whatever its disjuncts are: its cases are the two values of one of them
            truths = [state.get(child, (None,))[0] for child in _structure_children(structure)]
            unknown = truths.count(None)
            if True in truths or unknown < 2:
                continue
            if best is None or (unknown, position) < best[0]:
                best = ((unknown, position), structure, value[1])
        return None if best is None else best[1:]

    def _assign(self, state, lines, pending, structure, truth, proof, decides=None, typed=True):
        """Record a truth value with its proof; return a proof of False if it contradicts the state.

        A value already recorded with the same truth is left alone and its
        proof is dropped; `decides` names the atom whose decidability the
        proof uses, recorded as needed only when the proof is kept; a proof
        whose type Lean infers (typed False) gets a `have` without one.
        """
        if structure in state and state[structure][0] == truth:
            return None
        if decides is not None:
            self.needed.add(decides)
        if structure in state:
            positive, negative = (proof, state[structure][1]) if truth else (state[structure][1], proof)
            return "(%s %s)" % (negative, positive)
        self.steps += 1
        if proof not in self.names:  # a bare hypothesis or `have` name is reused, not restated
            name = self.name()
            if typed:
                rendered = self._render(structure)
                line = "have %s : %s := %s" % (name, rendered if truth else "(Not %s)" % rendered, proof)
            else:
                line = "have %s := %s" % (name, proof)
            self.chars += len(line)
            lines.append(line)
            proof = name
        state[structure] = (truth, proof)
        pending.append(structure)
        if self.relevant is None:
            pending.extend(self.parents[structure])
        else:  # the other gates draw no consequence (_consequences)
            pending.extend(parent for parent in self.parents[structure] if parent in self.relevant)
        return None

    def _propagate(self, state, lines, pending):
        while pending:
            if self._exhausted():
                return None
            structure = pending.pop()
            for target, truth, proof, decides, typed in self._consequences(state, structure, lines):
                conflict = self._assign(state, lines, pending, target, truth, proof, decides, typed)
                if conflict is not None:
                    return conflict
        return None

    def _tails(self, lines, proof, last):
        """Bind the rest of a true conjunction from every _AND_ELIM_STRIDE-th operand on, up to operand last.

        As _tail_lets does for and-elim: each tail projects from the one
        before, so projecting every operand of a conjunction takes one `.2`
        per operand plus at most a stride per projection. Projected from the
        proof itself, the conjuncts of a 400-operand assertion (a cnf lemma
        of QF_UF NEQ004) took 80,000 projections, longer in Lean than grind
        over the whole unfolded assertion. Returns the tail names by base.
        """
        tails = {0: proof}
        for base in range(_AND_ELIM_STRIDE, last + 1, _AND_ELIM_STRIDE):
            tails[base] = self.name()
            line = "have %s := %s%s" % (tails[base], tails[base - _AND_ELIM_STRIDE], ".2" * _AND_ELIM_STRIDE)
            self.chars += len(line)
            lines.append(line)
        return tails

    def _refuted_tails(self, lines, proof, last):
        """Bind the refutations of a false disjunction's tails from every _AND_ELIM_STRIDE-th operand on.

        The mirror of _tails: each tail is refuted from the one before by
        _AND_ELIM_STRIDE steps of mt Or.inr, so refuting every disjunct is
        linear in the width; from the refutation itself, disjunct i took i
        steps, and the 165 disjuncts of a flattened clock synchronization
        rewrite took 270,000 characters. Returns the tail names by base.
        """
        tails = {0: proof}
        for base in range(_AND_ELIM_STRIDE, last + 1, _AND_ELIM_STRIDE):
            tails[base] = self.name()
            line = "have %s := %s" % (tails[base], _reject_disjunct(_AND_ELIM_STRIDE, _AND_ELIM_STRIDE + 1,
                                                                     tails[base - _AND_ELIM_STRIDE]))
            self.chars += len(line)
            lines.append(line)
        return tails

    def _consequences(self, state, structure, lines):
        """The truth values one gate determines from its own value and its operands' values.

        Each consequence is (structure, truth, proof, decides, typed) where
        decides is the atom whose Decidable instance the proof uses, or
        None, and typed is whether the proof's `have` must state its type.
        The `have` lines binding the tails of a wide true conjunction go
        to lines, ahead of the consequences that project from them.
        """
        kind = structure[0]
        if kind in ("not", "and", "or", "implies", "iff") and not self._relevant(structure):
            return []
        children = _structure_children(structure)
        value = state.get(structure)
        values = [state.get(child) for child in children]
        truths = [None if v is None else v[0] for v in values]
        proofs = [None if v is None else v[1] for v in values]
        count = len(children)
        out = []

        def add(target, truth, proof, decides=None, typed=True):
            out.append((target, truth, proof, decides, typed))

        if kind == "not":
            (child,), (truth,), (proof,) = children, truths, proofs
            if value is not None:
                if value[0]:
                    add(child, False, value[1])
                elif self._negatable(child):
                    add(child, True, *self._by_contradiction(child, "%s _g" % value[1]))
            if truth is True:
                add(structure, False, "(fun _g => _g %s)" % proof)
            elif truth is False:
                add(structure, True, proof)
        elif kind == "and":
            if value is not None and value[0]:
                # A conjunct already true would be dropped by _assign; skipping it
                # here keeps a conjunction of n operands from building its n
                # projections each time one of them is assigned (cubic in n).
                positions = [i for i in range(count) if truths[i] is not True]
                tails = self._tails(lines, value[1], positions[-1]) if positions else {}
                for i in positions:
                    base = i // _AND_ELIM_STRIDE * _AND_ELIM_STRIDE
                    add(children[i], True, _select(i - base, count - base, tails[base]), typed=False)
            if value is not None and not value[0] and truths.count(None) == 1 and False not in truths:
                position = truths.index(None)
                parts = ["_g" if i == position else proof for i, proof in enumerate(proofs)]
                add(children[position], False,
                    "(fun (_g : %s) => %s %s)" % (self._render(children[position]), value[1],
                                                  _fold("And.intro", parts, "True.intro")), typed=False)
            if False in truths:
                position = truths.index(False)
                add(structure, False, _reject_conjunct(position, count, proofs[position]))
            elif None not in truths:
                add(structure, True, _fold("And.intro", proofs, "True.intro"), typed=False)
        elif kind == "or":
            if value is not None and not value[0]:
                positions = [i for i in range(count) if truths[i] is not False]  # as for a true conjunction
                tails = self._refuted_tails(lines, value[1], positions[-1]) if positions else {}
                for i in positions:
                    base = i // _AND_ELIM_STRIDE * _AND_ELIM_STRIDE
                    add(children[i], False, _reject_disjunct(i - base, count - base, tails[base]), typed=False)
            if value is not None and value[0] and truths.count(None) == 1 and True not in truths:
                position = truths.index(None)
                handlers = ["(fun _g => _g)" if i == position else "(fun _g => absurd _g %s)" % proof
                            for i, proof in enumerate(proofs)]
                add(children[position], True, _eliminate_or(value[1], handlers), typed=False)
            if True in truths:
                position = truths.index(True)
                add(structure, True, _inject(position, count, proofs[position]))  # typed: the operands follow
            elif None not in truths:
                add(structure, False, _reject_disjunction(proofs), typed=False)
        elif kind == "implies":
            (antecedent, consequent), (truth_a, truth_b), (proof_a, proof_b) = children, truths, proofs
            if antecedent == consequent:
                add(structure, True, "(fun _g => _g)")
            if value is not None and value[0]:
                if truth_a is True:
                    add(consequent, True, "(%s %s)" % (value[1], proof_a))
                if truth_b is False:
                    add(antecedent, False, "(fun _g => %s (%s _g))" % (proof_b, value[1]))
            if value is not None and not value[0]:
                add(consequent, False, "(fun _g => %s (fun _ => _g))" % value[1])
                if self._negatable(antecedent):
                    add(antecedent, True, *self._by_contradiction(
                        antecedent, "%s (fun _h => absurd _h _g)" % value[1]))
            if truth_a is False:
                add(structure, True, "(fun _g => absurd _g %s)" % proof_a)
            elif truth_b is True:
                add(structure, True, "(fun _ => %s)" % proof_b)
            elif truth_a is True and truth_b is False:
                add(structure, False, "(fun _g => %s (_g %s))" % (proof_b, proof_a))
        elif kind == "iff":
            (left, right), (truth_a, truth_b), (proof_a, proof_b) = children, truths, proofs
            if left == right:
                add(structure, True, "Iff.rfl")
            if value is not None and value[0] and self.scope is not None:
                # A sweep: the type follows from the fact, a link's theorem.
                if truth_a is True:
                    add(right, True, "(Iff.mp %s %s)" % (value[1], proof_a), typed=False)
                elif truth_a is False:
                    add(right, False, "(mt (Iff.mpr %s) %s)" % (value[1], proof_a), typed=False)
                if truth_b is True:
                    add(left, True, "(Iff.mpr %s %s)" % (value[1], proof_b), typed=False)
                elif truth_b is False:
                    add(left, False, "(mt (Iff.mp %s) %s)" % (value[1], proof_b), typed=False)
            elif value is not None and value[0]:
                if truth_a is True:
                    add(right, True, "(Iff.mp %s %s)" % (value[1], proof_a))
                elif truth_a is False:
                    add(right, False, "(fun _g => %s (Iff.mpr %s _g))" % (proof_a, value[1]))
                if truth_b is True:
                    add(left, True, "(Iff.mpr %s %s)" % (value[1], proof_b))
                elif truth_b is False:
                    add(left, False, "(fun _g => %s (Iff.mp %s _g))" % (proof_b, value[1]))
            if value is not None and not value[0]:
                if truth_a is True:
                    add(right, False, "(fun _g => %s (Iff.intro (fun _ => _g) (fun _ => %s)))"
                        % (value[1], proof_a))
                elif truth_a is False and self._negatable(right):
                    add(right, True, *self._by_contradiction(right, "%s (Iff.intro (fun _h => absurd _h %s) "
                                                             "(fun _h => absurd _h _g))" % (value[1], proof_a)))
                if truth_b is True:
                    add(left, False, "(fun _g => %s (Iff.intro (fun _ => %s) (fun _ => _g)))"
                        % (value[1], proof_b))
                elif truth_b is False and self._negatable(left):
                    add(left, True, *self._by_contradiction(left, "%s (Iff.intro (fun _h => absurd _h _g) "
                                                            "(fun _h => absurd _h %s))" % (value[1], proof_b)))
            if truth_a is not None and truth_b is not None:
                if truth_a and truth_b:
                    add(structure, True, "(Iff.intro (fun _ => %s) (fun _ => %s))" % (proof_b, proof_a))
                elif not truth_a and not truth_b:
                    add(structure, True, "(Iff.intro (fun _g => absurd _g %s) (fun _g => absurd _g %s))"
                        % (proof_a, proof_b))
                elif truth_a:
                    add(structure, False, "(fun _g => %s (Iff.mp _g %s))" % (proof_b, proof_a))
                else:
                    add(structure, False, "(fun _g => %s (Iff.mpr _g %s))" % (proof_a, proof_b))
        return out


def _structure_names(graph, memo):
    """The connective structures of the read nodes, named by the nodes' definitions.

    A step through a gate names the gate by its definition and Lean
    unfolds the definition when it unifies (the structure is what the
    definition reduces to), so no `let` binds the gates inside the proof
    and no `unfold` expands them in the goal: a cnf lemma over a 13,000-node
    assertion (QF_IDL BubbleSort) spent its heartbeats unfolding the 13,000
    definitions one at a time. Two nodes reading alike share a structure;
    either definition names it.
    """
    return {structure: _formula(graph, node) for node, structure in memo.items()
            if structure[0] in ("and", "or", "implies", "iff")}


def _structural_equivalence(graph, left, right, atom_indices):
    """Tactic lines proving the Boolean equivalence of two formulas, with the atoms it needs decidable."""
    memo = {}
    left, right = (_boolean_structure(graph, side, atom_indices, memo) for side in (left, right))
    prover = _PropositionalProver(left, right, names=_structure_names(graph, memo))
    return prover.equivalence(left, right), sorted(prover.needed)


def _cnf_lemma(graph, node, atom_indices, variable_indices):
    """Generate a Lean lemma for the exporter's cnf bridge: a clause the negated source assertions imply.

    The clause-log exporter ties an assumed clause that Z3 simplified before
    logging (a root ite's gate clause without the ite literal, a conjunct's
    clause under an asserted unit) to an unsat core of the assertions with a
    th-lemma of hint cnf: the clause of the negated sources followed by the
    assumed literals. Such a clause almost always follows from its sources
    by propositional reasoning alone, with the theory atoms opaque: Z3's
    clausification does not use what an atom denotes, except to normalize
    it (an equality's sides reordered, a comparison's complement). So the
    lemma is first proved by Classical.byContradiction and the gate
    propagation of _PropositionalProver over the Boolean structure of the
    clause, every theory atom a leaf, with every two leaves denoting one
    constraint, or complementary ones, bridged by an equivalence the theory
    tactic proves on its own (_leaf_bridges). A 3,500-character assertion
    (a conjunction of equalities, a 40-way disjunction, and ten Boolean ite
    terms over Int applications, QF_UFLIA Wisa) bridged to the gate clauses
    of its ite terms exhausted omega and grind over the unfolded formula
    (they split every ite and disjunction); the propagation proof is a
    tactic script of `have` steps over the gates named by their
    definitions (a 13,000-node circuit, QF_IDL BubbleSort, takes ten
    thousand of them, and neither unfolds the definitions nor nests the
    steps in one term: both exhausted the heartbeats). When the search
    gives up, it is repeated over the gates z3's unsat core of the
    propositional abstraction needs (_relevant_structures): over an
    assertion with a disjunction per time step (QF_IDL planning plan-21)
    the search took the earlier steps' disjunctions first and exhausted its
    budget, and over the core it splits the one step the clause is about.
    When the core's search gives up too, the clause is swept
    (_PropositionalProver.sweep): Z3 logged it over its rewriter's form of
    the assertion, and the two forms of a circuit (QF_IDL RTCL
    ckt_PROP1_tf_20, 4,000 gates each way) are related gate by gate, each
    link a small theorem before the lemma, where the search split without
    end. When no search refutes the clause, it rests on what the leaves
    denote beyond the bridges, and the search is repeated with theory
    clauses over the leaves (_theory_clauses), each a `have` the theory
    tactic proves, within _THEORY_CLAUSE_BUDGET times the limits; the proof
    kept is still at most _STRUCTURAL_REWRITE_CHARS long. The
    unfolded theory
    proof (_grind_lemma) stays the fallback, taken by `first` when the
    structural attempt is not found or does not check, and alone when the
    prover gives up (the clause needs a theory fact no theory clause
    supplies; the alldiff clauses Z3 simplified under a unit, which rest on
    the value of an ite of the sort under the distinct, took it until the
    oracle read uninterpreted terms).
    """
    conclusion = graph.conclusion(node)
    leaves, memo, synthetic = {}, {}, {}
    structure = _boolean_structure(graph, conclusion, atom_indices, memo, leaves, synthetic)
    bridges = _leaf_bridges(graph, leaves, synthetic)
    refutation, names, order, declarations = _cnf_refutation(graph, memo, structure, bridges, sweep=node)
    if declarations is not None:
        # Found by the sweep: the links are theorems of their own before
        # this one, and so are the bridges they rest on; the names are
        # those theorems applied, not hypotheses to state (there may be no
        # declaration at all: a clause refuted over the canonical gates it
        # is written in, without a bridge).
        lemma, term = _grind_lemma(graph, node, "th_lemma", atom_indices, variable_indices,
                                   opaque_tactic=_opaque_tactic(graph, node),
                                   structural=["refine Classical.byContradiction ?_"] + refutation)
        return declarations + lemma, term
    clauses = None
    if refutation is None:
        # The propositional abstraction may not refute the clause: once more
        # with the theory clauses over its leaves that do (_theory_clauses).
        clauses = _theory_clauses(graph, order, [("not", structure)] + [bridge for bridge, _ in bridges],
                                  atom_indices)
        if clauses:
            bridges = bridges + clauses
            refutation, names, _, _ = _cnf_refutation(graph, memo, structure, bridges, _THEORY_CLAUSE_BUDGET)
    if refutation is None:
        # A clause over products that Z3 assumed on its nonlinear solver's
        # word (nlsat) holds by what the products denote: by a polynomial
        # refutation when its literals are bounds over Int terms. Else by
        # the signs of the factors: an assertion over a product next to
        # the clause its rewritten form gives over the factors.
        return _grind_lemma(graph, node, "th_lemma", atom_indices, variable_indices,
                            opaque_tactic=_opaque_tactic(graph, node),
                            structural=_product_combination(graph, node) or _sign_split(graph, node))
    # The goal is the clause's definition, which the refutation's hypothesis
    # unifies with (its structure is named by that definition); nothing is
    # unfolded before the attempt, and the fallback unfolds everything. A
    # pair written the other way is the same equality reoriented (eq_comm,
    # the definition of a node side unfolded by unification).
    # The theory clauses come after the leaf bridges.
    bridged = len(bridges) - len(clauses or ())
    attempt = ["have %s : %s := %s" % (name, _render_structure(bridge), "eq_comm" if definitions is None else
                                       _theory_clause_proof(graph, bridge, definitions, position >= bridged))
               for position, ((bridge, definitions), name) in enumerate(zip(bridges, names))]
    attempt.append("refine Classical.byContradiction ?_")
    attempt.extend(refutation)
    if clauses and sum(len(line) + 1 for line in attempt) > _STRUCTURAL_REWRITE_CHARS:
        # The search over the theory clauses may look further, but the proof
        # kept stays within what the first searches could keep: a longer one
        # risks the lemma's heartbeats, which `first` does not catch (a
        # runtime exception fails the whole lemma, fallback included).
        attempt = None
    return _grind_lemma(graph, node, "th_lemma", atom_indices, variable_indices,
                        opaque_tactic=_opaque_tactic(graph, node), structural=attempt)


def _theory_clause_proof(graph, structure, definitions, clause):
    """The proof of a bridge or theory clause of a cnf lemma: the theory tactic over the unfolded leaves.

    A theory clause (_theory_clauses) over products of Int terms is first
    proved by the signs of their factors (_sign_split_clause), which the
    theory tactic does not find. The lines of that proof are indented past
    any column the `have` may start at.
    """
    unfolded = "unfold %s; %s" % (" ".join(definitions), _theory_tactic(graph))
    split = _sign_split_clause(graph, structure) if clause else None
    if split is None:
        return "by " + unfolded
    pad = "\n" + " " * 16
    return "by%sfirst%s  | (%s)%s  | (%s)" % (pad, pad, (pad + "     ").join(split), pad, unfolded)


def _cnf_refutation(graph, memo, structure, bridges, budget=1, sweep=None):
    """The prover's refutation of a cnf lemma's negated clause under the bridges, their names, and its structures.

    The search runs over every gate first and, when it gives up, once more
    over the gates z3's unsat core of the propositional abstraction needs
    (_relevant_structures), each within budget times the prover's limits.
    The refutation is None when neither finds one; the structures (children
    before parents) are the first prover's.

    With sweep, the node of the lemma, a clause neither search refutes is
    swept (_PropositionalProver.sweep). The fourth result is None unless
    the refutation is the sweep's: then it is the lines of the declarations
    to write before the lemma (possibly none), and the names are the
    bridges' theorems among them, applied.
    """
    facts = [("not", structure)] + [bridge for bridge, _ in bridges]
    relevant, order = None, None
    while True:
        prover = _PropositionalProver(*facts, classical=True, names=_structure_names(graph, memo), relevant=relevant,
                                      budget=budget)
        order = order or prover.order
        names = [prover.name() for _ in bridges]
        refutation = prover.refutation(("not", structure),
                                       [(bridge, name) for (bridge, _), name in zip(bridges, names)])
        if refutation is not None:
            return refutation, names, order, None
        if relevant is not None:
            break
        relevant = _relevant_structures(prover.order, facts)
        if relevant is None:
            return None, names, order, None
    if sweep is None:
        return None, names, order, None
    # The clause follows propositionally and the search is lost in it: the
    # sweep relates the two forms of the assertion gate by gate
    # (_PropositionalProver.sweep). Its links, the canonical gates they
    # state, and the bridges are declarations of their own, th_lemma_N_sK,
    # _kK, and _bK: a tactic block is elaborated within the heartbeats of
    # its declaration, and the links of a circuit take megabytes. The sweeps
    # of a file share _SWEEP_CHARS (graph.swept): Lean's memory grows with
    # the file.
    allowed = _SWEEP_CHARS - sum(chars for node, chars in graph.swept.items() if node != sweep)
    scope = ("th_lemma_%d" % sweep, " _atoms" + graph.valuation)
    binder = "(_atoms : Nat -> Prop)" + _valuation_binder(graph)
    prover = _PropositionalProver(*facts, classical=True, names=_structure_names(graph, memo), budget=budget,
                                  joined=[bridge for bridge, _ in bridges], scope=scope)
    stated = ["(%s_b%d%s)" % (scope[0], position, scope[1]) for position in range(len(bridges))]
    found = prover.sweep(("not", structure), [(bridge, name) for (bridge, _), name in zip(bridges, stated)],
                         chars=allowed)
    if found is None:
        return None, names, order, None
    declarations, refutation = found
    text = "\n".join(refutation + [line for _, statement, lines in declarations for line in [statement or ""] + lines])
    if len(text) > allowed:
        return None, names, order, None
    graph.swept[sweep] = len(text)
    lines = []
    for position, (bridge, definitions) in enumerate(bridges):
        if stated[position] in text:
            lines.extend(["", "set_option maxHeartbeats 1000000 in",
                          "private theorem %s_b%d %s" % (scope[0], position, binder),
                          "    : %s := %s" % (_render_structure(bridge), "eq_comm" if definitions is None else
                                              _theory_clause_proof(graph, bridge, definitions, False))])
    for name, statement, proof in declarations:
        if statement is None:
            lines.append("private def %s %s : Prop := %s" % (name, binder, proof[0]))
        else:
            lines.append("")
            if sum(map(len, proof)) > _SWEEP_LINK_CHARS // 10:
                lines.append("set_option maxHeartbeats 1000000 in")  # as a lemma has; the default is a fifth
            lines.extend(["private theorem %s %s" % (name, binder), "    : %s := by" % statement])
            lines.extend("  " + line for line in proof)
    return refutation, stated, order, lines


def _theory_clauses(graph, order, facts, atom_indices):
    """Theory clauses over the leaves that make the facts' propositional abstraction unsatisfiable, or None.

    A cnf lemma's clause may follow from its sources only by what the leaves
    denote, beyond the one-constraint bridges of _leaf_bridges. In QF_LRA
    tta_startup simple_startup_11nodes the assertion compares variables with
    Real ites whose conditions are 11-way conjunctions of Boolean atoms, and
    Z3 logs the clause over the rewriter's form of them: the conjunction
    flattened, (+ 0 x) as x, (= x 11) as (= 11 x), (ite c 0 0) as 0; and an
    ite's value follows from its condition, (= 10 x) gives (= (ite (= x 11)
    1 (+ x 1)) 11). The abstraction (every leaf and atom free) is
    satisfiable, the prover's search ends in a model, and the fallback grind
    over the unfolded clause (227 ites) ran out of heartbeats.

    The clauses are found as a lazy SMT solver finds theory lemmas: z3
    takes a model of the abstraction (order is the prover's structures,
    children before parents; facts are held true), the leaves' and atoms'
    values in it are checked against what the leaves denote, and an unsat
    core of those literals, shrunk one literal at a time, is a clause (its
    literals negated) that excludes the model; it is added and the search
    repeats until the abstraction is unsatisfiable. Each clause is returned
    as (structure, definitions), like a bridge: stated with a `have` that
    the theory tactic proves over the leaves' unfolded definitions, and
    given to the prover as a fact. z3 is an untrusted oracle here, as in
    _relevant_structures: a clause that does not hold is an error in Lean,
    which `first` catches, and the lemma keeps its fallback. A theory
    tactic that runs out of heartbeats is not caught (a runtime exception
    fails the whole lemma); the clauses are minimal cores, a clause over
    every leaf is not stated, and the kept proof is bounded (_cnf_lemma),
    but that is a heuristic, not a bound on the tactic. Uninterpreted
    functions, predicates, and sorts are declared in the oracle's context
    (_theory_function), so a clause may rest on congruence: an assertion
    over (ite c (f 0) (f 0)) and (+ 0 (g z)) is logged over (f 0) and
    (g z). A leaf whose meaning _theory_expression does not read (an array
    term, a datatype constructor) is free in the theory as in the
    abstraction.
    Returns [] when the abstraction is already unsatisfiable (the prover
    gave up within its limits), and None when a check is not decided within
    _THEORY_CLAUSE_RLIMIT, a model is consistent with the leaves (the clause
    does not hold, or rests on a leaf left free), a clause would range over
    every leaf (the lemma is one theory fact, the fallback's case), or
    _THEORY_CLAUSES clauses do not suffice.
    """
    context = z3.Context()
    abstraction, theory = z3.Solver(ctx=context), z3.Solver(ctx=context)
    for solver in (abstraction, theory):
        solver.set("rlimit", _THEORY_CLAUSE_RLIMIT)
    variables, literals, expressions = {}, {}, {}
    for index, structure in enumerate(order):
        kind = structure[0]
        if kind in ("true", "false"):
            variables[structure] = z3.BoolVal(kind == "true", context)
            continue
        if kind == "atom":
            variables[structure] = z3.Bool("a%d" % structure[1], context)
        else:
            variables[structure] = z3.Bool("s%d" % index, context)
        if kind in ("atom", "leaf"):
            literals[str(variables[structure])] = structure
            if kind == "leaf":
                if structure[1] >= 0:
                    meaning = _theory_expression(graph, structure[1], context, atom_indices, expressions)
                else:  # a synthetic pair leaf (a = b) of a distinct, see _distinct_pair_leaves
                    sides = [_theory_expression(graph, side, context, atom_indices, expressions)
                             for side in divmod(-structure[1] - 1, len(graph.nodes))]
                    meaning = None if any(side is None for side in sides) else sides[0] == sides[1]
                if meaning is not None:  # else a free leaf, as in the abstraction
                    theory.add(variables[structure] == meaning)
            continue
        children = [variables[child] for child in _structure_children(structure)]
        body = {"not": lambda: z3.Not(children[0]), "and": lambda: z3.And(children),
                "or": lambda: z3.Or(children), "implies": lambda: z3.Implies(children[0], children[1]),
                "iff": lambda: children[0] == children[1]}[kind]()
        abstraction.add(variables[structure] == body)
    abstraction.add(*[variables[fact] for fact in facts])
    leaves = sum(1 for structure in literals.values() if structure[0] == "leaf")
    clauses = []
    while True:
        result = abstraction.check()
        if result == z3.unsat:
            return clauses
        if result != z3.sat or len(clauses) == _THEORY_CLAUSES:
            return None
        model = abstraction.model()
        assignment = [variable if z3.is_true(model.eval(variable, model_completion=True)) else z3.Not(variable)
                      for variable in (variables[structure] for structure in literals.values())]
        if theory.check(*assignment) != z3.unsat:
            return None
        core, position = list(theory.unsat_core()), 0
        while position < len(core):
            if theory.check(*(core[:position] + core[position + 1:])) == z3.unsat:
                del core[position]
            else:
                position += 1
        abstraction.add(z3.Or([z3.Not(literal) for literal in core]))
        parts, nodes, used = [], set(), 0
        for literal in core:
            negated = z3.is_not(literal)
            structure = literals[str(literal.arg(0) if negated else literal)]
            parts.append(structure if negated else ("not", structure))
            if structure[0] == "leaf":
                used += 1
                nodes.update(divmod(-structure[1] - 1, len(graph.nodes)) if structure[1] < 0 else (structure[1],))
        if not used or used == leaves:
            # A clause over every leaf restates the lemma as one theory fact,
            # which the fallback proves with its helpers (scaled ite gates)
            # and the `have` would prove without them; over a wide distinct
            # as one leaf it ran omega out of heartbeats the same way.
            return None
        clauses.append((_structure_fold("or", parts), _definition_names(graph, _reachable(graph, *nodes)[0], nodes)))


_THEORY_EXPRESSIONS = {
    z3.Z3_OP_ADD: lambda args: z3.Sum(args), z3.Z3_OP_SUB: lambda args: args[0] - z3.Sum(args[1:]),
    z3.Z3_OP_UMINUS: lambda args: -args[0], z3.Z3_OP_MUL: lambda args: z3.Product(args),
    z3.Z3_OP_DIV: lambda args: args[0] / args[1], z3.Z3_OP_IDIV: lambda args: args[0] / args[1],
    z3.Z3_OP_MOD: lambda args: args[0] % args[1], z3.Z3_OP_TO_REAL: lambda args: z3.ToReal(args[0]),
    z3.Z3_OP_TO_INT: lambda args: z3.ToInt(args[0]), z3.Z3_OP_IS_INT: lambda args: z3.IsInt(args[0]),
    z3.Z3_OP_ABS: lambda args: z3.If(args[0] >= 0, args[0], -args[0]),
    z3.Z3_OP_LE: lambda args: args[0] <= args[1], z3.Z3_OP_GE: lambda args: args[0] >= args[1],
    z3.Z3_OP_LT: lambda args: args[0] < args[1], z3.Z3_OP_GT: lambda args: args[0] > args[1],
    z3.Z3_OP_EQ: lambda args: args[0] == args[1], z3.Z3_OP_DISTINCT: lambda args: z3.Distinct(args),
    z3.Z3_OP_ITE: lambda args: z3.If(args[0], args[1], args[2]), z3.Z3_OP_AND: lambda args: z3.And(args),
    z3.Z3_OP_OR: lambda args: z3.Or(args), z3.Z3_OP_NOT: lambda args: z3.Not(args[0]),
    z3.Z3_OP_IMPLIES: lambda args: z3.Implies(args[0], args[1]), z3.Z3_OP_XOR: lambda args: z3.Xor(args[0], args[1]),
}


def _theory_expression(graph, node, context, atom_indices, memo):
    """The z3 expression of a node in context, or None over a theory z3 is not given here.

    Boolean constants are the variables a<index> of their atom indices (the
    names _theory_clauses gives the atoms of its abstraction), Real and Int
    constants are v<declaration>, constants of an uninterpreted sort
    u<declaration>, and applications of an uninterpreted function or
    predicate apply f<declaration> (_theory_function); arrays, datatype
    constructors, and the other theories are not read. Nodes are
    converted bottom up on an explicit stack (deep chains), shared ones once
    (memo); an application's declaration is built once, when it is pushed
    (functions).
    """
    pending, functions = [(node, False)], {}
    while pending:
        current, expanded = pending.pop()
        if current in memo:
            continue
        decl, arguments = graph.decl(current), graph.arguments(current)
        if expanded:
            children = [memo[argument] for argument in arguments]
            if any(child is None for child in children):
                memo[current] = None
            elif decl.kind == z3.Z3_OP_XOR and len(children) != 2:
                memo[current] = None
            elif decl.kind == z3.Z3_OP_UNINTERPRETED:
                memo[current] = functions[current](*children)
            else:
                memo[current] = _THEORY_EXPRESSIONS[decl.kind](children)
        elif decl.kind == z3.Z3_OP_ANUM and decl.range in ("Int", "Real"):
            value = Fraction(decl.name)
            memo[current] = (z3.IntVal(int(value), context) if decl.range == "Int"
                             else z3.RealVal(value, context))
        elif decl.kind in (z3.Z3_OP_TRUE, z3.Z3_OP_FALSE):
            memo[current] = z3.BoolVal(decl.kind == z3.Z3_OP_TRUE, context)
        elif decl.kind == z3.Z3_OP_UNINTERPRETED and not arguments and decl.range == "Bool":
            memo[current] = z3.Bool("a%d" % atom_indices[graph.nodes[current].declaration], context)
        elif decl.kind == z3.Z3_OP_UNINTERPRETED and not arguments and decl.range in ("Int", "Real"):
            sort = z3.IntSort(context) if decl.range == "Int" else z3.RealSort(context)
            memo[current] = z3.Const("v%d" % graph.nodes[current].declaration, sort)
        elif decl.kind == z3.Z3_OP_UNINTERPRETED:
            function = _theory_function(graph, current, context)
            if function is None:
                memo[current] = None
            elif not arguments:
                memo[current] = function()
            else:
                functions[current] = function
                pending.append((current, True))
                pending.extend((argument, False) for argument in arguments)
        elif decl.kind in _THEORY_EXPRESSIONS and arguments:
            pending.append((current, True))
            pending.extend((argument, False) for argument in arguments)
        else:
            memo[current] = None
    return memo[node]


def _theory_function(graph, node, context):
    """The z3 declaration of node's uninterpreted constant, function, or predicate in context, or None.

    A constant of an uninterpreted sort is u<declaration>, a function or
    predicate f<declaration>, over Bool, Int, Real, and the uninterpreted
    sorts, each declared by its name (an enumeration sort too: its
    constructors are not read, so the oracle knows less about it than Lean
    does, never more). None over an array sort.
    """
    decl = graph.decl(node)
    names = decl.domain + (decl.range,)
    if any(name not in ("Bool", "Int", "Real") and name not in graph.carriers for name in names):
        return None
    sorts = [{"Bool": z3.BoolSort, "Int": z3.IntSort, "Real": z3.RealSort}[name](context)
             if name in ("Bool", "Int", "Real") else z3.DeclareSort(name, context) for name in names]
    return z3.Function(("f%d" if decl.domain else "u%d") % graph.nodes[node].declaration, *sorts)


def _leaf_bridges(graph, leaves, synthetic=None):
    """Equivalences between leaves of one constraint key, or of complementary keys, with the definitions to unfold.

    Z3's rewriter orders the sides of an equality and writes a strict
    comparison as the negation of its complement, so the assumed clause's
    literal and the assertion's atom it comes from can be two nodes
    denoting one constraint (or complementary ones); generalized apart they
    are unrelated and propagation stops at them. Each bridge is the
    structure ("iff", leaf, other) or ("iff", leaf, ("not", other)), to be
    stated as a `have` the theory tactic proves (the sides' definitions
    unfolded) and given to the prover as a fact. Returns (structure,
    definition names) pairs.

    A synthetic pair leaf (a, b) of a distinct (_distinct_pair_leaves, by
    id in synthetic) is bridged to the leaf of the node (= b a), or to the
    synthetic leaf (b, a) of another distinct, once per unordered pair:
    ("iff", (a = b), (b = a)), with None for the definitions, as eq_comm
    proves it.
    """
    by_key, bridges, joined = {}, [], set()
    keyed = [(leaf, _leaf_key(graph, leaf)) for leaf in sorted(leaves)]
    for leaf, (key, _) in keyed:
        by_key.setdefault(key, []).append(leaf)
    for members in by_key.values():
        # A chain through the group: propagation crosses it in both directions.
        bridges.extend((first, second, False) for first, second in zip(members, members[1:]))
    for leaf, (key, complement) in keyed:
        # One bridge, between the first leaves, joins two complementary
        # groups; the chains carry it to their other members.
        if complement in by_key and frozenset((key, complement)) not in joined:
            joined.add(frozenset((key, complement)))
            bridges.append((leaf, by_key[complement][0], True))
    result = []
    for leaf, other, negated in bridges:
        definitions = _definition_names(graph, _reachable(graph, leaf)[0] | _reachable(graph, other)[0],
                                        (leaf, other))
        right = ("not", leaves[other]) if negated else leaves[other]
        result.append((("iff", leaves[leaf], right), definitions))
    for identifier, leaf in sorted((synthetic or {}).items(), reverse=True):
        left, right = divmod(-identifier - 1, len(graph.nodes))
        swapped = graph.equalities.get((right, left))
        if swapped is not None:
            other = leaves.get(swapped)  # in the clause, the node is a leaf
        elif (right, left) < (left, right):
            other = synthetic.get(-(1 + right * len(graph.nodes) + left))
        else:
            other = None
        if other is not None:
            result.append((("iff", leaf, other), None))
    return result


def _leaf_key(graph, leaf):
    """The constraint a theory atom denotes, and the one its negation denotes (None when not linear).

    An arithmetic atom is keyed by its linear constraint with coprime
    integer coefficients (positive leading one for an equality), over Int
    with the bound of a non-strict constraint rounded to an integer (so
    (<= (* 2 x) (* 2 y)) and (<= x y), whose tightened complements differ
    by the scaling, key alike), the complement likewise; an equality over
    the uninterpreted sort by its two sides unordered; anything else by
    itself.
    """
    kind, arguments = graph.kind(leaf), graph.arguments(leaf)
    if kind == z3.Z3_OP_EQ and not graph.is_arith(arguments[0]):
        return ("eq", frozenset(arguments)), None
    if kind not in _ARITH_PREDICATE_NAMES and kind != z3.Z3_OP_EQ:
        return ("leaf", leaf), None
    keys = []
    for polarity in (True, False):
        try:
            relation, terms, constant = _polarity_constraint(graph, leaf, polarity)
        except ReconstructionError:
            keys.append(("leaf", leaf) if polarity else None)
            continue
        if not terms:
            keys.append((relation, (), constant))
            continue
        denominators = functools.reduce(math.lcm, (value.denominator for value in terms.values()), 1)
        numerators = functools.reduce(math.gcd, (abs(int(value * denominators)) for value in terms.values()))
        scale = Fraction(denominators, numerators)
        if relation == "=" and terms[min(terms)] < 0:
            scale = -scale
        constant *= scale
        if relation == "<=" and graph.integer_form(terms):
            constant = Fraction(math.ceil(constant))  # terms + constant <= 0 with integer terms
        keys.append((relation, tuple(sorted((variable, value * scale) for variable, value in terms.items())),
                     constant))
    return tuple(keys)


def _rewrite_lemma(graph, node, atom_indices, variable_indices=None, terms=None):
    """Generate a Lean lemma for a rewrite step, checked independently of the assertions.

    A propositional rewrite is proved by a tactic script of gate propagation
    and case splits on atoms over the folded goal (_PropositionalProver); the
    exhaustive truth table over the atoms' decidability witnesses, exponential
    in their number, is the fallback when the prover gives up. Theory
    rewrites go to grind, except that a rewrite between two identical
    formulas (the legacy core records one per assertion) is Iff.refl.
    """
    conclusion = graph.conclusion(node)
    left, right = _equivalence(graph, conclusion, "rewrite")
    reachable, theory = _reachable(graph, conclusion)
    pseudo_boolean = any(graph.kind(formula) in _PSEUDO_BOOLEAN for formula in reachable)
    if (theory or pseudo_boolean) and terms is not None and terms[left] == terms[right]:
        return [], set(), "(%s.refl %s)" % (_relation(graph, left), _side(graph, left))
    if pseudo_boolean:
        lines, term = _pseudo_boolean_lemma(graph, node, "rewrite", atom_indices)
        return lines, set(), term
    distinct = _negated_distinct_rewrite(graph, node, left, right)
    if distinct is not None:
        return distinct, set(), "(rewrite_%d _atoms%s)" % (node, graph.valuation)
    if graph.is_term(left):
        # A rewrite between terms (the legacy core simplifies ite terms, for
        # example (ite true a b) to a): a theory tautology for grind.
        lines, term = _grind_lemma(graph, node, "rewrite", atom_indices, variable_indices,
                                   opaque_tactic=_opaque_rewrite_tactic(graph))
        return lines, set(), term
    if theory:
        # The atoms and connectives outside the ite terms: the normalized
        # rewrite leaves an ite whole, so the formulas in its condition are
        # neither atoms nor connectives of its propositional lemma.
        outside = _reachable_outside(graph, conclusion, _arith_ites(graph, reachable))
        atoms = [formula for formula in sorted(outside)
                 if graph.kind(formula) in _ARITH_PREDICATE_NAMES.keys() | {z3.Z3_OP_EQ}
                 and graph.arguments(formula) and graph.is_arith(graph.arguments(formula)[0])]
        distinct = any(graph.kind(formula) == z3.Z3_OP_DISTINCT for formula in reachable)
        if (len(atoms) > _NORMALIZED_REWRITE_ATOMS and not distinct
                and _normalizable_rewrite(graph, node, outside, atoms)):
            lines, term = _normalized_rewrite(graph, node, outside, atoms, atom_indices, variable_indices)
        else:
            # The rewriter's sign split of a factored product: by the signs of
            # the factors first. Else a regrouping of the gates over the same
            # theory atoms: by the structure of the two sides.
            lines, term = _grind_lemma(graph, node, "rewrite", atom_indices, variable_indices,
                                       opaque_tactic=_opaque_rewrite_tactic(graph),
                                       structural=(_sign_split(graph, node, rewrite=True)
                                                   or _leaf_equivalence(graph, left, right, atom_indices)))
        return lines, set(), term
    proof, atoms = _structural_equivalence(graph, left, right, atom_indices)
    if proof is None:
        atoms = sorted(atom_indices[graph.nodes[formula].declaration]
                       for formula in reachable if graph.kind(formula) == z3.Z3_OP_UNINTERPRETED)
    lines = ["", "private theorem rewrite_%d (_atoms : Nat -> Prop)%s" % (node, _valuation_binder(graph))]
    for atom in atoms:
        lines.append("    [_d%d : Decidable (_atoms %d)]" % (atom, atom))
    lines.append("    : %s := by" % _formula(graph, conclusion))
    if proof is not None:
        # The goal stays folded: the proof names the gates by their definitions.
        lines.extend("  " + line for line in proof)
        term = "(@rewrite_%d _atoms%s%s)" % (node, graph.valuation, "".join(" _d%d" % atom for atom in atoms))
        return lines, atoms, term
    lines.append("  unfold " + " ".join("formula_%d" % formula for formula in sorted(reachable, reverse=True)))
    for atom in atoms:
        lines.extend([
            "  all_goals",
            "    cases _d%d <;> rename_i _h%d <;>" % (atom, atom),
            "      (first | letI : Decidable (_atoms %d) := .isFalse _h%d" % (atom, atom),
            "             | letI : Decidable (_atoms %d) := .isTrue _h%d)" % (atom, atom),
        ])
    lines.append("  all_goals exact of_decide_eq_true rfl")
    term = "(@rewrite_%d _atoms%s%s)" % (node, graph.valuation, "".join(" _d%d" % atom for atom in atoms))
    return lines, atoms, term


def _leaf_equivalence(graph, left, right, atom_indices):
    """Tactic lines proving a rewrite between two formulas by their Boolean structure alone, or None.

    Every theory atom (an equality or a distinct over terms, a comparison,
    a predicate application) is an opaque leaf, the same leaf where the two
    sides share the node, and the goal stays folded, as for a cnf lemma
    (_cnf_lemma): the proof names the gates by their definitions. Z3's
    rewriter flattens the nested conjunctions and disjunctions of an
    assertion, sorts their operands and drops the duplicates, which the
    prover's links relate (_equivalent_structures). Such a rewrite went to
    grind over the unfolded sides, which case-splits the disjunctions: the
    quasigroup inputs of QF_UF QG-classification (a five-way disjunction of
    conjunctions of 20 or 25 clauses over the equalities of a 5 by 5
    operation table, written as binary gates and logged flattened) ran out
    of the heartbeats in each such rewrite, 0.5 to 3 MB certificates that
    Lean rejected after 20 to 85 s.

    Only for a rewrite over more than _NORMALIZED_REWRITE_ATOMS leaves, the
    size from which the rewrites over arithmetic atoms leave grind too
    (_normalized_rewrite), and only when the prover finds the proof: a
    rewrite that rests on what an atom denotes (an equality reoriented or
    decided) gets none here and goes to the theory tactic as before, which
    is the fallback of this attempt as well.
    """
    leaves, memo = {}, {}
    try:
        sides = [_boolean_structure(graph, side, atom_indices, memo, leaves) for side in (left, right)]
    except ReconstructionError:
        return None
    if len(leaves) <= _NORMALIZED_REWRITE_ATOMS:
        return None
    prover = _PropositionalProver(*sides, classical=True, names=_structure_names(graph, memo), links=True)
    return prover.equivalence(*sides)


def _negated_distinct_rewrite(graph, node, left, right):
    """The lemma lines of the rewrite of a negated distinct into the disjunction of its pairs, or None.

    Z3's rewriter turns (not (distinct a1 ... an)) into (or (= a1 a2) (= a1
    a3) ... (= an-1 an)), the pairs in the order _formula_body renders the
    distinct's conjuncts (Not (ai = aj)). The proof peels one conjunct and
    one disjunct per step, De Morgan and a double negation (an equality
    written (= aj ai) also takes eq_comm), so it is linear in the number of
    pairs: grind over the unfolded sides ran out of heartbeats on the 780
    pairs of a 40-term distinct over Int. None for any other shape, which
    goes to grind as before.
    """
    if graph.kind(left) != z3.Z3_OP_NOT:
        return None
    distinct = graph.arguments(left)[0]
    arguments = graph.arguments(distinct)
    if (graph.kind(distinct) != z3.Z3_OP_DISTINCT or len(arguments) < 3
            or not graph.is_term(arguments[0]) or graph.kind(right) != z3.Z3_OP_OR):
        return None
    pairs = [(first, second) for index, first in enumerate(arguments) for second in arguments[index + 1:]]
    disjuncts = graph.arguments(right)
    if len(disjuncts) != len(pairs):
        return None
    congruences = []
    for (first, second), disjunct in zip(pairs, disjuncts):
        if graph.kind(disjunct) != z3.Z3_OP_EQ:
            return None
        sides = tuple(graph.arguments(disjunct))
        if sides == (first, second):
            congruences.append("Classical.not_not")
        elif sides == (second, first):
            congruences.append("(Classical.not_not.trans eq_comm)")
        else:
            return None
    conclusion = graph.conclusion(node)
    lines = ["", "private theorem rewrite_%d (_atoms : Nat -> Prop)%s" % (node, _valuation_binder(graph)),
             "    : %s := by" % _formula(graph, conclusion),
             "  unfold %s" % " ".join("formula_%d" % formula for formula in (conclusion, left, distinct, right))]
    lines.extend("  refine Iff.trans Classical.not_and_iff_not_or_not (or_congr %s ?_)" % congruence
                 for congruence in congruences[:-1])
    lines.append("  exact %s" % congruences[-1])
    return lines


def _normalizable_rewrite(graph, node, reachable, atoms):
    """Whether _normalized_rewrite can separate the atoms from the Boolean structure.

    The linear forms of the atoms may range over variables and over opaque
    terms without a formula inside (applications of uninterpreted
    functions, div, mod), which _normalized_rewrite keys by node. An atom
    whose canonical key (_normalized_atom) occurs on one side of the
    rewrite only may range over variables alone: the propositional lemma
    then proves its disappearance, as it did before opaque terms were
    admitted. With an opaque term in it, such an atom signals that Z3's
    rewriter reasoned about the term, which the lemma over abstract atoms
    cannot: it decides (< (mod x 10) 0) from the bounds of mod, and it
    simplifies inside a function's arguments, (f (+ x 0)) to (f x), so
    that the two sides' atoms differ by more than their linear form. An
    ite term is opaque as a whole, keyed by its value table
    (_ite_representatives), since the rewriter reshapes ite terms, (ite
    (not c) a b) to (ite c b a), merging nested conditions and normalizing
    the atoms in them; an ite without a table is excluded. An abs, logged
    as (ite (>= t 0) t (- t)), has a table, but its rewrite still goes to
    grind: one side keys the opaque (abs t) and the other the ite, so the
    two sides' atom keys differ. reachable holds the formulas outside the
    ite terms. Every
    other formula must be a connective or a Boolean variable, as the
    propositional lemma binds the atoms alone. Anything else goes to grind
    as before.
    """
    def formula_free(term):
        pending, seen = [term], set()
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            if not graph.is_term(current):
                return False
            pending.extend(graph.arguments(current))
        return True

    representatives = _ite_representatives(graph, atoms)

    def order(variable):
        # Any total order keys two atoms alike exactly when _normalized_rewrite's does.
        if not graph.arguments(variable):
            return 0, variable
        return 1, representatives.get(variable, variable)

    atom_set = set(atoms)
    for formula in reachable:
        if formula in atom_set or graph.is_term(formula):
            continue
        kind, arguments = graph.kind(formula), graph.arguments(formula)
        if kind == z3.Z3_OP_UNINTERPRETED:
            if arguments:
                return False
        elif kind == z3.Z3_OP_EQ:
            if graph.is_term(arguments[0]):
                return False
        elif kind not in _NORMALIZED_CONNECTIVES:
            return False
    try:
        keys = []
        for side in graph.arguments(graph.conclusion(node)):
            side_reachable = _reachable_outside(graph, side, representatives)
            keys.append({_normalized_atom(graph, atom, order)[0] for atom in atoms if atom in side_reachable})
    except ReconstructionError:
        return False
    opaque = {term for side in keys for _, ordered, _ in side for (kind, term), _ in ordered if kind == 1}
    if any(term not in representatives and not formula_free(term) for term in opaque):
        return False
    left, right = keys
    return all(kind == 0 for _, ordered, _ in left ^ right for (kind, _), _ in ordered)


def _int_atom(graph, atom):
    """Whether an arithmetic atom, under any negations, compares Int terms (and is tightened, _polarity_constraint)."""
    while graph.kind(atom) == z3.Z3_OP_NOT:
        atom = graph.arguments(atom)[0]
    return graph.is_int(graph.arguments(atom)[0])


def _normalized_atom(graph, atom, order):
    """The canonical key of an arithmetic atom's linear form, and whether the atom is its negation.

    The key is (relation, ((order(term), coefficient), ...), constant) with
    the terms sorted by order and the first one's coefficient scaled to 1
    (its absolute value for <=), so that positive multiples of one
    constraint share a key. Over Int every atom is already tightened to
    t <= 0, whose complement is -t + 1 <= 0: a form with a negative leading
    coefficient is keyed as the negation of its complement, so that (< x 5)
    and (>= x 5) share one atom (the replay's _Normalizer does the same)
    and the propositional lemma sees them as complementary. A Real atom
    whose form ranges over Int terms alone (through to_real, qf_lira) is
    not tightened by _atom_constraint, so it is tightened here first:
    scaled to integer coefficients and constant, a strict t < 0 made
    t + 1 <= 0, and rounded to the lattice (_rounded), after which it keys
    like the equivalent Int atom and the complement step is valid.
    """
    relation, terms, constant = _atom_constraint(graph, atom)
    if relation != "=" and terms and graph.integer_form(terms) and not _int_atom(graph, atom):
        scale = _common_denominator(terms, constant)
        terms, constant = {var: value * scale for var, value in terms.items()}, constant * scale
        if relation == "<":
            relation, constant = "<=", constant + 1
        terms, constant = _rounded(terms, constant)
    negated = relation == "<"
    if negated:
        terms, constant, relation = {var: -value for var, value in terms.items()}, -constant, "<="
    first = min(terms, key=order) if terms else None
    if relation == "<=" and terms and terms[first] < 0 and graph.integer_form(terms):
        terms, constant, negated = {var: -value for var, value in terms.items()}, -constant + 1, True
    if terms:
        scale = terms[first] if relation == "=" else abs(terms[first])
        terms, constant = {var: value / scale for var, value in terms.items()}, constant / scale
    ordered = tuple(sorted((order(var), value) for var, value in terms.items()))
    return (relation, ordered, constant), negated


def _arith_ites(graph, nodes):
    """The Real or Int ite terms among nodes."""
    return {node for node in nodes if graph.kind(node) == z3.Z3_OP_ITE and graph.is_arith(node)}


def _numeral_ite(graph, term):
    """Whether term is an arithmetic ite whose branches are, through nested ites, constant linear forms."""
    if graph.kind(term) != z3.Z3_OP_ITE or not graph.is_arith(term):
        return False
    pending, seen = [term], set()
    while pending:
        node = pending.pop()
        if node in seen:
            continue
        seen.add(node)
        if graph.kind(node) == z3.Z3_OP_ITE:
            pending.extend(graph.arguments(node)[1:])
            continue
        terms = {}
        try:
            _linear_term(graph, node, Fraction(1), terms)
        except ReconstructionError:
            return False
        if any(terms.values()):
            return False
    return True


# Rewrites that evaluate connectives and ites once their Boolean leaves are True or False.
_LEAF_EVALUATION_LEMMAS = (
    "not_true_eq_false, not_false_eq_true, and_true, true_and, and_false, false_and, or_true, true_or, "
    "or_false, false_or, true_implies, false_implies, implies_true, true_iff, iff_true, false_iff, iff_false, "
    "ite_true, ite_false")


def _ite_leaf_split(graph, ites, atom_indices):
    """A `first` alternative proving a goal over ites by cases on their conditions' Boolean variables.

    Each case rewrites the variables to True or False; simp then evaluates
    the conditions, decides comparisons of numerals (an evaluated atom of
    _ite_table) and reduces the ites to their branches, and grind closes the
    linear rest. Empty without Boolean variables or with more than
    _ITE_TABLE_LEAVES of them (2^n cases).
    """
    variables = set()
    for ite in ites:
        variables |= {node for node in _reachable(graph, ite)[0]
                      if graph.kind(node) == z3.Z3_OP_UNINTERPRETED and not graph.arguments(node)
                      and not graph.is_term(node)}
    indices = sorted({atom_indices[graph.nodes[node].declaration] for node in variables})
    if not indices or len(indices) > _ITE_TABLE_LEAVES:
        return []
    cases = " <;> ".join("by_cases _c%d : _atoms %d" % (index, index) for index in indices)
    names = ", ".join("_c%d" % index for index in indices)
    return ["    | (%s <;>" % cases,
            "        simp (config := { decide := true }) only [%s, %s] <;> grind)" % (
                names, _LEAF_EVALUATION_LEMMAS)]


def _ite_representatives(graph, atoms):
    """Map each ite term under the atoms that has a value table to the least ite of the same table.

    The table (_ite_table) is the ite's value, a linear form, under every
    assignment of its condition leaves; two ites of one table denote the
    same number, whatever the leaves' values, so a normalized rewrite keys
    them as one opaque term (the lemma of an atom over the other one proves
    them equal; nothing is assumed). Ids are topological, so an ite nested
    in another's branch or condition is keyed first; an ite of more than
    _ITE_TABLE_LEAVES leaves, or with a condition that is not over Boolean
    variables and linear atoms, has no table and no entry.
    """
    ites = set()
    for atom in atoms:
        ites |= _arith_ites(graph, _reachable(graph, atom)[0])
    representatives, tables = {}, {}

    def order(variable):
        if not graph.arguments(variable):
            return 0, graph.nodes[variable].declaration
        return 1, representatives.get(variable, variable)

    for ite in sorted(ites):
        try:
            table = _ite_table(graph, ite, order)
        except ReconstructionError:
            continue
        # By sort too: in qf_lira an Int and a Real ite over numerals tabulate alike.
        representatives[ite] = tables.setdefault((graph.decl(ite).range, table), ite)
    return representatives


def _ite_table(graph, ite, order):
    """The leaves of an ite's conditions and its linear-form value under each of their assignments.

    A leaf is a Boolean variable or the canonical key of a linear atom
    (_normalized_atom), so (< x 3) and (not (<= 3 x)) are one leaf. The
    leaves are treated as independent, which only makes fewer ites equal.
    An atom over ite terms of numeral values alone (_numeral_ite), such as
    (= (ite c 4 (ite d 3 0)) 4), is no leaf but evaluated: its leaves are
    those of the inner ites' conditions. Z3's rewriter decides such atoms,
    turning (ite (= (ite c 4 ...) 4) 20 ...) into (ite (or c ...) 20 ...)
    (the sal/carpark QF_LRA benchmarks), which the two tables now key alike.
    """
    numeral_atoms = {}

    def evaluated(node):
        """The constraint of an atom over numeral-valued ites, or None for a leaf."""
        if node not in numeral_atoms:
            relation, terms, constant = _atom_constraint(graph, node)
            numeral = bool(terms) and all(_numeral_ite(graph, term) for term in terms)
            numeral_atoms[node] = (relation, terms, constant) if numeral else None
        return numeral_atoms[node]

    leaves, pending, seen = set(), [ite], set()
    while pending:
        node = pending.pop()
        if node in seen:
            continue
        seen.add(node)
        if len(seen) > _ITE_TABLE_NODES:
            raise ReconstructionError("ite %d has too large conditions" % ite)
        kind, arguments = graph.kind(node), graph.arguments(node)
        if graph.is_term(node):
            if kind == z3.Z3_OP_ITE:
                pending.extend(arguments)
        elif kind == z3.Z3_OP_UNINTERPRETED and not arguments:
            leaves.add(("bool", graph.nodes[node].declaration))
        elif kind in _ARITH_PREDICATE_NAMES or (kind == z3.Z3_OP_EQ and graph.is_arith(arguments[0])):
            constraint = evaluated(node)
            if constraint is None:
                leaves.add(_normalized_atom(graph, node, order)[0])
            else:
                pending.extend(constraint[1])
        elif kind in _NORMALIZED_CONNECTIVES or (kind == z3.Z3_OP_EQ and len(arguments) == 2
                                                 and not graph.is_term(arguments[0])):
            pending.extend(arguments)
        else:
            raise ReconstructionError("no value table for ite %d" % ite)
    names = sorted(leaves, key=repr)
    if len(names) > _ITE_TABLE_LEAVES:
        raise ReconstructionError("ite %d has too many condition leaves" % ite)

    def holds(node, values):
        kind, arguments = graph.kind(node), graph.arguments(node)
        if kind == z3.Z3_OP_UNINTERPRETED:
            return values[("bool", graph.nodes[node].declaration)]
        if kind in _ARITH_PREDICATE_NAMES or (kind == z3.Z3_OP_EQ and graph.is_arith(arguments[0])):
            constraint = evaluated(node)
            if constraint is None:
                key, negated = _normalized_atom(graph, node, order)
                return values[key] != negated
            relation, terms, constant = constraint
            constant += sum(coefficient * numeral_value(term, values) for term, coefficient in terms.items())
            return constant == 0 if relation == "=" else constant <= 0 if relation == "<=" else constant < 0
        operands = [holds(argument, values) for argument in arguments]
        if kind == z3.Z3_OP_TRUE:
            return True
        if kind == z3.Z3_OP_FALSE:
            return False
        if kind == z3.Z3_OP_NOT:
            return not operands[0]
        if kind == z3.Z3_OP_AND:
            return all(operands)
        if kind == z3.Z3_OP_OR:
            return any(operands)
        if kind == z3.Z3_OP_IMPLIES:
            return not operands[0] or operands[1]
        if kind in (z3.Z3_OP_IFF, z3.Z3_OP_EQ):
            return operands[0] == operands[1]
        if kind == z3.Z3_OP_XOR:
            return operands[0] != operands[1]
        return operands[1] if operands[0] else operands[2]  # a Boolean ite

    def numeral_value(node, values):
        while graph.kind(node) == z3.Z3_OP_ITE:
            condition, then_branch, else_branch = graph.arguments(node)
            node = then_branch if holds(condition, values) else else_branch
        return _linear_term(graph, node, Fraction(1), {})

    def value(node, values):
        while graph.kind(node) == z3.Z3_OP_ITE:
            condition, then_branch, else_branch = graph.arguments(node)
            node = then_branch if holds(condition, values) else else_branch
        terms = {}
        constant = _linear_term(graph, node, Fraction(1), terms)
        return tuple(sorted((order(term), coefficient) for term, coefficient in terms.items() if coefficient)), constant

    table = []
    for bits in range(1 << len(names)):
        values = {name: bool(bits >> position & 1) for position, name in enumerate(names)}
        table.append(value(ite, values))
    return tuple(names), tuple(table)


def _normalized_rewrite(graph, node, reachable, atoms, atom_indices, variable_indices):
    """Separate linear atom normalization from propositional rewrite search.

    Each atom is rewritten to a canonical linear form bound as a Prop,
    `_atomN`, the same name for atoms of one key and `(Not _atomN)` for the
    complement. The theory tactic proves each rewrite in a lemma of its own,
    `normalized_atom_N_A`: as `have`s of one theorem, every grind call saw
    the atoms and rewrites before it in its context and all shared one
    heartbeat budget, which a conjunction of 1,100 bounds exhausted about
    200 atoms in; each lemma now has the budget the whole theorem had.
    The Boolean lemma over the names, `normalized_rewrite_N`, is proved by
    _PropositionalProver in
    classical mode (the names are leaves, a constant atom its truth value)
    with `grind` as the `first` fallback, and `simpa` closes the rewrite
    with it. The 74-way disjunction of the clock synchronization QF_LRA
    benchmark, flattened by Z3 to 48 disjuncts with the duplicates and the
    conjuncts false by a constant atom dropped, is where `grind` alone
    failed. The prover links the sides' structures equal up to flattening
    first (_equivalent_structures), so the 250-way disjunction of the
    8-clock variant is proved too.

    An ite term is one opaque term of the linear forms, an ite and its
    reshaped counterpart on the other side (_ite_representatives) rendered
    alike: the lemma of an atom over the other proves the two ites equal
    by grind's case splits on their few conditions, so the reshaping is
    checked atom by atom and the propositional lemma never sees it.
    """
    representatives = _ite_representatives(graph, atoms)

    def order(variable):
        # Variables by index, then opaque terms by node, an ite by its
        # representative's (see _normalizable_rewrite).
        if not graph.arguments(variable):
            index = variable_indices[graph.nodes[variable].declaration]
            variables[index] = variable
            return 0, index
        return 1, representatives.get(variable, variable)

    variables = {}  # variable index -> its node, for its valuation (_variable)

    def render(key):
        kind, index = key
        if kind == 0:
            return _variable(graph, variables[index], index)
        return "(%s)" % _inline(graph, index, atom_indices, variable_indices)

    canonical, normalized_atoms, rewrites, atom_lemmas, lines = {}, {}, [], [], [
        "", "set_option maxHeartbeats 1000000 in",
        "set_option linter.unnecessarySimpa false in",
        "private theorem rewrite_%d (_atoms : Nat -> Prop)%s" % (node, _valuation_binder(graph)),
        "    : %s := by" % _formula(graph, graph.conclusion(node)),
    ]
    for atom in atoms:
        key, negated = _normalized_atom(graph, atom, order)
        relation, ordered, constant = key
        scale = 1
        for value in [value for _, value in ordered] + [constant]:
            scale = scale * value.denominator // _gcd(scale, value.denominator)
        sort = graph.decl(graph.arguments(atom)[0]).range
        parts = ["(%s * %s)" % (_numeral(sort, value * scale), render(var)) for var, value in ordered]
        parts.append(_numeral(sort, constant * scale))
        expression = "(%s %s ((0 : %s)))" % (" + ".join(parts), relation, _NUMBER_TYPES[sort])
        if not ordered:
            holds = constant == 0 if relation == "=" else constant <= 0
            expression = "True" if holds != negated else "False"
            negated = False
        name = canonical.get(key) if ordered else expression
        if name is None:
            name = "_atom%d" % len(canonical)
            canonical[key] = name
            lines.append("  let %s : Prop := %s" % (name, expression))
        target = "(Not %s)" % name if negated else name
        normalized_atoms[atom] = target
        expanded = "(Not %s)" % expression if negated else expression
        rewrite = "_norm%d" % atom
        rewrites.append(rewrite)
        # Over an ite term, grind alone fails to prove two ites equal whose
        # conditions are an iff or xor of an atom and a Boolean variable;
        # splitting every ite of the goal first leaves linear goals. Nor
        # does either prove an ite over (= (ite c 4 ...) 4) conditions equal
        # to its counterpart over c (_ite_table evaluates such atoms): a case
        # split on the Boolean variables of the conditions, after which simp
        # evaluates every condition and ite over them, does.
        ites = _arith_ites(graph, _reachable(graph, atom)[0])
        tactic, split = ["  grind"], []
        if ites:
            split = _ite_leaf_split(graph, ites | {representatives.get(ite, ite) for ite in ites}, atom_indices)
            tactic = ["  first", "    | grind"] + split + ["    | ((repeat' split) <;> grind)"]
        # Not every case of the split uses every simp argument.
        atom_lemmas.extend([""] + (["set_option linter.unusedSimpArgs false in"] if split else []) + [
            "set_option maxHeartbeats 1000000 in",
            "private theorem normalized_atom_%d_%d (_atoms : Nat -> Prop)%s" % (
                node, atom, _valuation_binder(graph)),
            "    : %s <-> %s := by" % (_formula(graph, atom), expanded),
            "  change %s <-> %s" % (_inline(graph, atom, atom_indices, variable_indices), expanded),
        ] + tactic)
        lines.append("  have %s : %s <-> %s := normalized_atom_%d_%d _atoms%s" % (
            rewrite, _formula(graph, atom), target, node, atom, graph.valuation))
    definitions = ["formula_%d" % formula for formula in sorted(reachable, reverse=True)
                   if not graph.is_arith(formula) and formula not in atoms]
    names = list(canonical.values())
    structures = {}

    def structure(root):
        """The Boolean structure over the normalized atoms: a leaf per name, a constant for a constant atom.

        Read bottom up on an explicit stack, as _boolean_structure does.
        """
        pending = [(root, False)]
        while pending:
            formula, expanded = pending.pop()
            if formula in structures:
                continue
            target = normalized_atoms.get(formula)
            if target is not None:
                negated = target.startswith("(Not ")
                name = target[5:-1] if negated else target
                # A leaf's identity is its atom index (an int, as the split order sorts it with the Boolean atoms).
                leaf = (("true",) if name == "True" else ("false",) if name == "False"
                        else ("leaf", int(name[len("_atom"):]), name))
                structures[formula] = ("not", leaf) if negated else leaf
            elif graph.kind(formula) == z3.Z3_OP_UNINTERPRETED:
                structures[formula] = ("atom", atom_indices[graph.nodes[formula].declaration])
            elif expanded:
                structures[formula] = _boolean_connective(
                    graph.kind(formula), [structures[arg] for arg in graph.arguments(formula)])
            else:
                pending.append((formula, True))
                pending.extend((arg, False) for arg in reversed(graph.arguments(formula)))
        return structures[root]

    left, right = (structure(side) for side in graph.arguments(graph.conclusion(node)))
    prover = _PropositionalProver(left, right, classical=True, links=True)
    equivalence = prover.equivalence(left, right)
    boolean_lemma = [
        "", "set_option maxHeartbeats 1000000 in",
        "private theorem normalized_rewrite_%d (_atoms : Nat -> Prop)%s" % (
            node, "".join(" (%s : Prop)" % name for name in names)),
        "    : %s :=" % _render_structure(("iff", left, right)),
    ]
    if equivalence is not None:
        boolean_lemma.extend(["  by first", "    | (" + "\n       ".join(equivalence) + ")",
                              "    | grind (splits := 64)"])
    else:
        boolean_lemma.append("  by grind (splits := 64)")
    lines.append("  simpa only [%s] using (normalized_rewrite_%d _atoms %s)" % (
        ", ".join(definitions + rewrites), node, " ".join(names)))
    return atom_lemmas + boolean_lemma + lines, "(rewrite_%d _atoms%s)" % (node, graph.valuation)


def _gate_contradiction(graph, formula, truth, proof, fact):
    """Refute one Boolean gate using only facts about its immediate operands."""
    kind, args = graph.kind(formula), graph.arguments(formula)
    pos = [fact(arg, True) for arg in args]
    neg = [fact(arg, False) for arg in args]
    if kind == z3.Z3_OP_AND:
        if truth:
            for position, evidence in enumerate(neg):
                if evidence is not None:
                    return "(%s %s)" % (evidence, _project(position, len(args), proof))
        elif all(evidence is not None for evidence in pos):
            return "(%s %s)" % (proof, _fold("And.intro", pos, "True.intro"))
    elif kind == z3.Z3_OP_OR:
        if truth and all(evidence is not None for evidence in neg):
            if not args:
                return proof
            branch = neg[-1]
            for evidence in reversed(neg[:-1]):
                branch = "(fun _tail => Or.elim _tail %s %s)" % (evidence, branch)
            return "(%s %s)" % (branch, proof)
        if not truth:
            for position, evidence in enumerate(pos):
                if evidence is not None:
                    return "(%s %s)" % (proof, _inject(position, len(args), evidence))
    elif kind == z3.Z3_OP_IMPLIES:
        if truth and pos[0] and neg[1]:
            return "(%s (%s %s))" % (neg[1], proof, pos[0])
        if not truth and neg[0]:
            return "(%s (fun _arg => False.elim (%s _arg)))" % (proof, neg[0])
        if not truth and pos[1]:
            return "(%s (fun _arg => %s))" % (proof, pos[1])
    elif kind in (z3.Z3_OP_EQ, z3.Z3_OP_IFF):
        if truth:
            if pos[0] and neg[1]:
                return "(%s (Iff.mp %s %s))" % (neg[1], proof, pos[0])
            if pos[1] and neg[0]:
                return "(%s (Iff.mpr %s %s))" % (neg[0], proof, pos[1])
        elif all(pos):
            return "(%s (Iff.intro (fun _arg => %s) (fun _arg => %s)))" % (proof, pos[1], pos[0])
        elif all(neg):
            return ("(%s (Iff.intro (fun _arg => False.elim (%s _arg))"
                    " (fun _arg => False.elim (%s _arg))))") % (proof, neg[0], neg[1])
    elif kind == z3.Z3_OP_XOR and len(args) == 1:
        # (xor p) is p: the gate clauses are (or (xor p) (not p)) and (or (not (xor p)) p).
        if truth and neg[0]:
            return "(%s %s)" % (neg[0], proof)
        if not truth and pos[0]:
            return "(%s %s)" % (proof, pos[0])
    elif kind == z3.Z3_OP_XOR:
        if truth and all(pos):
            return ("(Or.elim %s (fun _pair => (And.right _pair) %s)"
                    " (fun _pair => (And.left _pair) %s))") % (proof, pos[1], pos[0])
        if truth and all(neg):
            return ("(Or.elim %s (fun _pair => %s (And.left _pair))"
                    " (fun _pair => %s (And.right _pair)))") % (proof, neg[0], neg[1])
        if not truth and pos[0] and neg[1]:
            return "(%s (Or.inl (And.intro %s %s)))" % (proof, pos[0], neg[1])
        if not truth and neg[0] and pos[1]:
            return "(%s (Or.inr (And.intro %s %s)))" % (proof, neg[0], pos[1])
    elif kind == z3.Z3_OP_ITE:
        if truth and pos[0] and neg[1]:
            return ("(Or.elim %s (fun _pair => %s (And.right _pair))"
                    " (fun _pair => (And.left _pair) %s))") % (proof, neg[1], pos[0])
        if truth and neg[0] and neg[2]:
            return ("(Or.elim %s (fun _pair => %s (And.left _pair))"
                    " (fun _pair => %s (And.right _pair)))") % (proof, neg[0], neg[2])
        if not truth and pos[0] and pos[1]:
            return "(%s (Or.inl (And.intro %s %s)))" % (proof, pos[0], pos[1])
        if not truth and neg[0] and pos[2]:
            return "(%s (Or.inr (And.intro %s %s)))" % (proof, neg[0], pos[2])
        # Z3 also records the two condition-free gate clauses: both branches
        # false refutes the ite, both true establishes it (constructively,
        # since a true then-branch turns the first disjunct's refutation into
        # a refutation of the condition).
        if truth and neg[1] and neg[2]:
            return ("(Or.elim %s (fun _pair => %s (And.right _pair))"
                    " (fun _pair => %s (And.right _pair)))") % (proof, neg[1], neg[2])
        if not truth and pos[1] and pos[2]:
            return "(%s (Or.inr (And.intro (fun _cond => %s (Or.inl (And.intro _cond %s))) %s)))" % (
                proof, proof, pos[1], pos[2])
    return None


def _distinct_gate_contradiction(graph, terms, distinct, truth, proof, facts, formulas):
    """Refute a distinct over terms against the disjunction of its pairwise equalities.

    The sat.smt core's alldiff clauses relate a distinct d below the root to
    some_eq, the or of equalities between its arguments: (or d some_eq) and
    (or (not d) (not some_eq)). d unfolds to the conjunction of the pairwise
    disequalities. With d and some_eq both held, every disjunct must equate
    two arguments of d (in either orientation) and is refuted by the pair's
    conjunct; with both denied, every pair must have a disjunct, which
    builds d. Any other disjunct, or a missing pair, leaves the clause
    unproved (the exporter accepts the same two shapes).
    """
    arguments = graph.arguments(distinct)
    pairs = [(terms[left], terms[right])
             for index, left in enumerate(arguments) for right in arguments[index + 1:]]
    for key, other in facts.items():
        some_eq = formulas[key]
        if key[1] != truth or some_eq == distinct:
            continue
        disjuncts = graph.arguments(some_eq) if graph.kind(some_eq) == z3.Z3_OP_OR else [some_eq]
        if not disjuncts:
            continue
        matches = []  # (pair position, flipped) per disjunct
        for disjunct in disjuncts:
            operands = graph.arguments(disjunct)
            if graph.kind(disjunct) != z3.Z3_OP_EQ or len(operands) != 2 or not graph.is_term(operands[0]):
                break
            left, right = terms[operands[0]], terms[operands[1]]
            if (left, right) in pairs:
                matches.append((pairs.index((left, right)), False))
            elif (right, left) in pairs:
                matches.append((pairs.index((right, left)), True))
            else:
                break
        else:
            if truth:
                refutations = ["(fun _eq => %s %s)" % (_project(position, len(pairs), proof),
                                                        "(Eq.symm _eq)" if flipped else "_eq")
                               for position, flipped in matches]
                branch = refutations[-1]
                for refutation in reversed(refutations[:-1]):
                    branch = "(fun _tail => Or.elim _tail %s %s)" % (refutation, branch)
                return "(%s %s)" % (branch, other)
            covering = {}  # pair position -> (first disjunct index equating it, flipped)
            for index, (position, flipped) in enumerate(matches):
                covering.setdefault(position, (index, flipped))
            if len(covering) == len(pairs):
                conjuncts = []
                for position in range(len(pairs)):
                    index, flipped = covering[position]
                    conjuncts.append("(fun _eq => %s %s)" % (
                        other, _inject(index, len(disjuncts), "(Eq.symm _eq)" if flipped else "_eq")))
                return "(%s %s)" % (proof, _fold("And.intro", conjuncts, "True.intro"))
    return None


def _ite_gate_lemma(graph, terms, node):
    """Prove a clause tying a Real or uninterpreted-sort ite to one branch, or return None.

    The two gate clauses of (ite c a b) are (not c) or (ite c a b) = a and
    c or (ite c a b) = b, with either equality orientation, in any literal
    order, and possibly weakened. The proof splits on a decidability witness
    for the condition's innermost negand p (c itself when it is not a
    negation) and rewrites the ite with ite_eq_left or ite_eq_right. The
    split is on p rather than on c because Z3 logs the gates of
    (ite (not p) a b) with the double negation collapsed, p or ... = a, and
    because a split on p proves c and (not c) by lifting without eliminating
    any double negation, so the lemma stays axiom-free. When p is the
    constant true or false and the clause has no guard literal (Z3 states the
    guard, the negation of a constant, as false), there is nothing to split
    on: the equation of the case that holds proves the clause, without a
    decidability witness (_ite_gate_decided).
    """
    conclusion = graph.conclusion(node)
    literals = graph.clause(conclusion)
    for position, literal in enumerate(literals):
        if graph.kind(literal) != z3.Z3_OP_EQ or not graph.is_term(graph.arguments(literal)[0]):
            continue
        left, right = graph.arguments(literal)
        for ite, branch, flipped in ((left, right, False), (right, left, True)):
            if graph.kind(ite) != z3.Z3_OP_ITE:
                continue
            condition, then_branch, else_branch = graph.arguments(ite)
            core, depth = _negation_core(graph, condition)
            # Both sides are tried when the branches are one term, (ite c a a):
            # the clause may then be either gate, or the bare equality
            # (ite c a a) = a that Z3 logs as a tseitin step, proved by cases
            # without any guard literal. Each side's equation holds in the
            # case of the split where its witness (c or (not c)) holds: the
            # one of the parity of that witness's negations over p.
            sides = [("(%s %s)" % (rule, _lift_negations(parity)), parity)
                     for rule, parity, selected in (("ite_eq_left", depth, then_branch),
                                                    ("ite_eq_right", depth + 1, else_branch))
                     if terms[branch] == terms[selected]]
            for equation, parity in sides:
                gate = _ite_gate_case(graph, terms, node, literals, position, core, equation, parity, flipped)
                if gate is not None:
                    return gate
            if len(sides) == 2:
                cases = [None, None]
                for equation, parity in sides:
                    if flipped:
                        equation = "(Eq.symm %s)" % equation
                    cases[parity % 2] = _inject(position, len(literals), equation)
                return _ite_gate_by_cases(graph, node, core, cases)
            # A condition whose negand is the constant true or false decides
            # the ite, and Z3 logs its gate without a guard: the guard would
            # be the negation of a constant, which the clause states as false,
            # (or false (= (ite true a b) a)). Z3 meets such an ite only in
            # assertions it logs unsimplified, those after one that folds to
            # false. The equation of the case that holds proves the clause.
            decided = {z3.Z3_OP_TRUE: 0, z3.Z3_OP_FALSE: 1}.get(graph.kind(core))
            for equation, parity in sides:
                if parity % 2 == decided:
                    if flipped:
                        equation = "(Eq.symm %s)" % equation
                    return _ite_gate_decided(graph, node, core, decided,
                                             _inject(position, len(literals), equation))
    return None


def _negation_core(graph, formula):
    """Return (p, count): the formula under its outermost negations, and how many there were."""
    count = 0
    while graph.kind(formula) == z3.Z3_OP_NOT:
        formula, count = graph.arguments(formula)[0], count + 1
    return formula, count


def _lift_negations(count):
    """A proof of p under count negations from _hc : p (count even) or _hnc : Not p (count odd).

    Each pair of negations is one application to the hypothesis: from
    _hc : p, (fun _n0 => _n0 _hc) : Not (Not p). Nothing is eliminated, so no
    decidability beyond the split's witness is needed.
    """
    evidence = "_hc" if count % 2 == 0 else "_hnc"
    for level in range(count // 2):
        evidence = "(fun _n%d => _n%d %s)" % (level, level, evidence)
    return evidence


def _ite_gate_by_cases(graph, node, core, cases):
    """The gate lemma as a case split on the decidability witness of p, the condition's negand.

    cases[0] proves the clause from _hc : p and cases[1] from _hnc : Not p.
    """
    conclusion = graph.conclusion(node)
    lines = [
        "",
        "private theorem def_axiom_%d (_atoms : Nat -> Prop)%s" % (node, _valuation_binder(graph)),
        "    [_df%d : Decidable %s]" % (core, _formula(graph, core)),
        "    : %s :=" % _formula(graph, conclusion),
        "  @Decidable.byCases %s _ _df%d (fun _hc => %s) (fun _hnc => %s)" % (
            _formula(graph, core), core, cases[0], cases[1]),
    ]
    term = "(@def_axiom_%d _atoms%s _df%d)" % (node, graph.valuation, core)
    return lines, {core}, term


def _ite_gate_decided(graph, node, core, parity, case):
    """The gate lemma of an ite whose condition's negand p is the constant true (parity 0) or false (1).

    case proves the clause from _hc : p (parity 0) or from _hnc : Not p
    (parity 1); the hypothesis holds outright, so the lemma needs neither a
    split nor a decidability witness.
    """
    hypothesis, evidence = (("_hc : %s", "True.intro"), ("_hnc : Not %s", "(fun _false => _false)"))[parity]
    lines = [
        "",
        "private theorem def_axiom_%d (_atoms : Nat -> Prop)%s" % (node, _valuation_binder(graph)),
        "    : %s :=" % _formula(graph, graph.conclusion(node)),
        "  (fun (%s) => %s) %s" % (hypothesis % _formula(graph, core), case, evidence),
    ]
    return lines, set(), "(@def_axiom_%d _atoms%s)" % (node, graph.valuation)


def _ite_gate_case(graph, terms, node, literals, position, core, equation, parity, flipped):
    """The gate lemma for one orientation of the ite equality, or None when its guard literal is absent.

    The equation holds in the case of parity (negations over p) given; the
    guard literal is the opposite witness, p under any number of negations
    of the other parity (Z3 collapses double negations, so (not (not p))
    arrives as p), and holds in the other case.
    """
    if flipped:
        equation = "(Eq.symm %s)" % equation
    for guard_position, guard in enumerate(literals):
        guard_core, guard_depth = _negation_core(graph, guard)
        if terms[guard_core] != terms[core] or guard_depth % 2 == parity % 2:
            continue
        cases = [None, None]
        cases[parity % 2] = _inject(position, len(literals), equation)
        cases[guard_depth % 2] = _inject(guard_position, len(literals), _lift_negations(guard_depth))
        return _ite_gate_by_cases(graph, node, core, cases)
    return None


def _gate_key(graph, terms, node, cache):
    """A key identifying formulas whose Lean renderings are definitionally equal.

    distinct over terms unfolds to the same right-nested conjunction of
    disequalities as the and of (not (= ...)) atoms the legacy core pairs it
    with in its gate clauses, and a nested conjunction renders like a flat
    one; everything else is identified by its interned structure.
    """
    if node in cache:
        return cache[node]
    kind, arguments = graph.kind(node), graph.arguments(node)
    if kind == z3.Z3_OP_DISTINCT and arguments and graph.is_term(arguments[0]):
        conjuncts = [("not", ("eq", terms[left], terms[right]))
                     for index, left in enumerate(arguments) for right in arguments[index + 1:]]
    elif kind == z3.Z3_OP_AND:
        conjuncts = [_gate_key(graph, terms, argument, cache) for argument in arguments]
    elif kind == z3.Z3_OP_NOT:
        conjuncts = None
        key = ("not", _gate_key(graph, terms, arguments[0], cache))
    elif kind == z3.Z3_OP_EQ and arguments and graph.is_term(arguments[0]):
        conjuncts = None
        key = ("eq", terms[arguments[0]], terms[arguments[1]])
    else:
        conjuncts = None
        key = ("atom", terms[node])
    if conjuncts is not None:
        key = ("true",)
        for conjunct in reversed(conjuncts):
            key = conjunct if key == ("true",) else ("and", conjunct, key)
    cache[node] = key
    return key


def _def_axiom_lemma(graph, terms, node):
    """Prove a Boolean gate clause independently of all input assertions."""
    gate = _ite_gate_lemma(graph, terms, node)
    if gate is not None:
        return gate
    conclusion = graph.conclusion(node)
    literals = graph.clause(conclusion)
    facts, formulas, steps, support, keys = {}, {}, [], {conclusion}, {}

    def fact_key(formula, truth):
        return _gate_key(graph, terms, formula, keys), truth

    for position, literal in enumerate(literals):
        evidence = "_lit%d" % position
        steps.append("  let %s : Not %s := fun _value => _not_clause %s" % (
            evidence, _formula(graph, literal), _inject(position, len(literals), "_value")))
        formula, truth = literal, False
        while graph.kind(formula) == z3.Z3_OP_NOT:
            formula = graph.arguments(formula)[0]
            if not truth:
                support.add(formula)
                evidence = "(@Decidable.byContradiction %s _df%d %s)" % (
                    _formula(graph, formula), formula, evidence)
            truth = not truth
        key = fact_key(formula, truth)
        facts.setdefault(key, evidence)
        formulas.setdefault(key, formula)

    def fact(formula, truth):
        negations = []
        while graph.kind(formula) == z3.Z3_OP_NOT:
            negations.append(truth)
            formula, truth = graph.arguments(formula)[0], not truth
        evidence = facts.get(fact_key(formula, truth))
        if evidence is None:
            if graph.kind(formula) == z3.Z3_OP_TRUE and truth:
                evidence = "True.intro"
            elif graph.kind(formula) == z3.Z3_OP_FALSE and not truth:
                evidence = "(fun _false => _false)"
            else:
                return None
        for truth in reversed(negations):
            if not truth:
                evidence = "(fun _neg => _neg %s)" % evidence
        return evidence

    contradiction = None
    for key, evidence in facts.items():
        formula, truth = formulas[key], key[1]
        opposite = fact(formula, not truth)
        if opposite is not None:
            contradiction = "(%s %s)" % ((opposite, evidence) if truth else (evidence, opposite))
        elif graph.kind(formula) == z3.Z3_OP_DISTINCT and graph.arguments(formula) and graph.is_term(graph.arguments(formula)[0]):
            contradiction = _distinct_gate_contradiction(graph, terms, formula, truth, evidence, facts, formulas)
        else:
            contradiction = _gate_contradiction(graph, formula, truth, evidence, fact)
        if contradiction is not None:
            break
    if contradiction is None:
        raise ReconstructionError("unsupported or invalid def-axiom clause at node %d" % node)
    support = sorted(support)
    lines = ["", "private theorem def_axiom_%d (_atoms : Nat -> Prop)%s" % (node, _valuation_binder(graph))]
    lines.extend("    [_df%d : Decidable %s]" % (formula, _formula(graph, formula)) for formula in support)
    lines.extend([
        "    : %s :=" % _formula(graph, conclusion),
        "  @Decidable.byContradiction %s _df%d fun _not_clause =>" % (_formula(graph, conclusion), conclusion),
    ])
    lines.extend(steps)
    lines.append("  " + contradiction)
    term = "(@def_axiom_%d _atoms%s%s)" % (node, graph.valuation,
                                         "".join(" _df%d" % formula for formula in support))
    return lines, support, term


def _linear_term(graph, node, scale, terms):
    """Accumulate the linear form of a Real or Int node into terms; return its constant part.

    Variables, ite terms, integer div, mod, and rem, abs, and to_int are
    the atoms of the linear form; each is opaque to Farkas reasoning, an
    ite tied to its branches by gate clauses and a div, mod, rem, or to_int
    to its operands by the solver's arith axioms. A product of two or more
    nonconstant factors is an atom too, the node as it stands (Z3's simplex
    solver has one variable for it); nothing ties it to its factors here,
    and Lean, whose * it is, normalizes polynomials in grind.
    """
    kind = graph.kind(node)
    arguments = graph.arguments(node)
    if kind == z3.Z3_OP_ANUM:
        return scale * Fraction(graph.decl(node).name)
    if kind in _DIVISION_KINDS:
        _integer_divisor(graph, node)
    if kind in _LINEAR_ATOM_KINDS:
        terms[node] = terms.get(node, Fraction(0)) + scale
        return Fraction(0)
    if kind == z3.Z3_OP_ADD:
        return sum((_linear_term(graph, arg, scale, terms) for arg in arguments), Fraction(0))
    if kind == z3.Z3_OP_SUB:
        return (_linear_term(graph, arguments[0], scale, terms)
                + sum((_linear_term(graph, arg, -scale, terms) for arg in arguments[1:]), Fraction(0)))
    if kind == z3.Z3_OP_UMINUS:
        return _linear_term(graph, arguments[0], -scale, terms)
    if kind == z3.Z3_OP_MUL:
        variable, factors = None, scale
        for arg in arguments:
            factor_terms = {}
            factor = _linear_term(graph, arg, Fraction(1), factor_terms)
            if factor_terms:
                if variable is not None:
                    # A second nonconstant factor: the product is an atom,
                    # its numeral factors included.
                    terms[node] = terms.get(node, Fraction(0)) + scale
                    return Fraction(0)
                variable = arg
            else:
                factors *= factor
        scale = factors
        if variable is None:
            return scale
        return _linear_term(graph, variable, scale, terms)
    if kind == z3.Z3_OP_DIV:
        divisor = _linear_term(graph, arguments[1], Fraction(1), {})
        if divisor == 0:
            raise ReconstructionError("division by zero in a theory lemma")
        return _linear_term(graph, arguments[0], scale / divisor, terms)
    if kind == z3.Z3_OP_TO_REAL:
        # The injection commutes with sums and numeral products: (to_real t)
        # has t's linear form, over t's Int atoms (see _cast_facts).
        return _linear_term(graph, arguments[0], scale, terms)
    raise ReconstructionError("unsupported arithmetic term in a theory lemma")


def _is_product(graph, node):
    """Whether a node is a product of two or more nonconstant factors, an atom of the linear forms.

    A factor is constant when it is a numeral expression, as (+ 1 2) and
    (* 2 3): one whose linear form has no atom (_linear_term).
    """
    return (graph.kind(node) == z3.Z3_OP_MUL and graph.is_arith(node)
            and sum(_numeral_expression_value(graph, arg) is None for arg in graph.arguments(node)) > 1)


def _integer_divisor(graph, node):
    """Return the nonzero constant divisor of an Int div, mod, or rem node, rejecting any other.

    Lean's Int / and % are total (x / 0 = 0) where SMT-LIB leaves div and mod
    by zero uninterpreted, so a zero divisor would prove the input
    unsatisfiable under one interpretation only; a nonconstant divisor is
    nonlinear. _validate_graph applies this to every such node, not only to
    those under theory lemmas.
    """
    terms = {}
    divisor = _linear_term(graph, graph.arguments(node)[1], Fraction(1), terms)
    if terms or divisor == 0:
        raise ReconstructionError("integer %s by a nonconstant or zero divisor at node %d" % (
            graph.decl(node).name, node))
    return divisor


def _atom_constraint(graph, atom):
    """Return (relation, terms, constant) for an arithmetic atom that holds."""
    return _polarity_constraint(graph, atom, True)


def _linear_constraint(graph, literal):
    """Return (relation, terms, constant) for the constraint a clause literal denies.

    The clause literal is the negation of a hint literal, so the constraint is
    the one that holds when the clause literal is false.
    """
    return _polarity_constraint(graph, literal, False)


def _polarity_constraint(graph, literal, polarity):
    atom = literal
    while graph.kind(atom) == z3.Z3_OP_NOT:
        atom, polarity = graph.arguments(atom)[0], not polarity
    kind, arguments = graph.kind(atom), graph.arguments(atom)
    if (kind not in _ARITH_PREDICATE_NAMES and kind != z3.Z3_OP_EQ) or not graph.is_arith(arguments[0]):
        raise ReconstructionError("th-lemma literal is not a linear arithmetic atom")
    left, right = arguments
    if kind == z3.Z3_OP_EQ:
        if not polarity:
            raise ReconstructionError("th-lemma coefficients cannot use a disequality")
        relation, first, second = "=", left, right
    else:
        if kind in (z3.Z3_OP_GE, z3.Z3_OP_GT):
            left, right, kind = right, left, {z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_GT: z3.Z3_OP_LT}[kind]
        strict = kind == z3.Z3_OP_LT
        if polarity:
            relation, first, second = ("<" if strict else "<="), left, right
        else:
            relation, first, second = ("<=" if strict else "<"), right, left
    terms = {}
    constant = _linear_term(graph, first, Fraction(1), terms) + _linear_term(graph, second, Fraction(-1), terms)
    terms = {k: v for k, v in terms.items() if v != 0}
    if graph.is_int(left):
        # Over Int a strict constraint is its tightened non-strict form, as in
        # Z3's checker; the exporter's replay keys atoms the same way.
        try:
            return integer_tightened(relation, terms, constant)
        except ProofExportError as error:
            raise ReconstructionError(str(error)) from None
    return relation, terms, constant


def _check_th_lemma(graph, node):
    """Check Farkas combinations and implied-equality shapes before calling Lean.

    A clause-log th-lemma has no premises and its coefficients weight the
    complements of the clause literals. A legacy th-lemma lists the literals
    and equalities theory_lra's conflict or propagation rests on as premises
    and concludes false, the propagated literal, or the implied equality; the
    coefficients weight the premises first, then the clause literals. Lean
    proves the implication from the premises either way.
    """
    parameters = graph.decl(node).parameters
    premises = [graph.conclusion(premise) for premise in graph.arguments(node)[:-1]]
    literals = list(graph.clause(graph.conclusion(node)))
    if parameters[0] == "triangle-eq":
        _check_triangle_eq(graph, node, premises, literals)
        return
    if parameters[0] == "array":
        # An array axiom instance: a clause of (dis)equalities between terms
        # of an array, index, or element sort, without premises.
        if premises or not literals or not graph.arrays:
            raise ReconstructionError("array th-lemma must be a clause over arrays without premises at node %d" % node)
        # Int, Real, or Bool terms are compared only if some array is indexed
        # by or holds that sort (Bool: the elements of a set, the store
        # axiom's (= v (select (store a i v) i)) over formulas, or the
        # indices of an array over Bool, (= i j) between formulas).
        components = {component for sort in graph.arrays for component in _array_components(sort)}
        for literal in literals:
            atom = graph.arguments(literal)[0] if graph.kind(literal) == z3.Z3_OP_NOT else literal
            if graph.kind(atom) == z3.Z3_OP_SET_SUBSET:
                # The array solver's own axiom of a subset it was given as
                # written (after an assertion that folds to false): (subset
                # a b) against (= (setminus a b) empty), one clause each way.
                continue
            if (graph.kind(atom) != z3.Z3_OP_EQ
                    or graph.decl(graph.arguments(atom)[0]).range not in components | set(graph.sorts)):
                raise ReconstructionError("array th-lemma literals must be equalities over arrays and their sorts "
                                          "at node %d" % node)
        # The default-map axiom, (= (default (map f a b)) (f (default a)
        # (default b))): _default of an array that is not constant at all
        # but finitely many indices is an arbitrary value, so no theorem
        # states it of the default values an input names (the exporter
        # leaves the axiom out or rejects the refutation). It is a theorem
        # of the default values read at a generic index (_generic_defaults).
        if not graph.generic and _default_map_axiom(graph, node):
            raise ReconstructionError("the default value of a map is not certified at node %d" % node)
        return
    if parameters[0] == "datatype":
        # The datatype solver's clauses over an enumeration: equalities
        # between its terms (constructors included) and recognizers, proved
        # by Lean from the enumeration fields.
        if premises or not literals:
            raise ReconstructionError("datatype th-lemma must be a clause without premises at node %d" % node)
        for literal in literals:
            atom = graph.arguments(literal)[0] if graph.kind(literal) == z3.Z3_OP_NOT else literal
            if (graph.kind(atom) not in (z3.Z3_OP_EQ, z3.Z3_OP_DT_IS)
                    or graph.decl(graph.arguments(atom)[0]).range not in graph.enumerations):
                raise ReconstructionError("datatype th-lemma literal is not an enumeration equality at node %d"
                                          % node)
        return
    if parameters[0] == "arith":
        # The arithmetic solver's own axioms (div and mod definitions), a
        # clause of linear arithmetic atoms without premises, and the legacy
        # core's cuts, the bound a Gomory or Hermite cut derives from the
        # premises it lists (held linear atoms). No coefficients certify
        # either; the theory tactic proves the clause or the implication.
        # Unlike the cut path, polarity is ignored: the equality axiom is a
        # positive equality in the clause, which _linear_constraint would
        # refuse as a denied equality, and no combination is formed here.
        if not literals:
            raise ReconstructionError("arith th-lemma must conclude a clause at node %d" % node)
        for premise in premises:
            _atom_constraint(graph, premise)
        for literal in literals:
            atom = literal
            while graph.kind(atom) == z3.Z3_OP_NOT:
                atom = graph.arguments(atom)[0]
            if graph.kind(atom) == z3.Z3_OP_FALSE and literal == atom:
                continue  # The legacy core's axioms are stated as (or false l).
            if graph.kind(atom) == z3.Z3_OP_IS_INT:
                # The is_int definition's axioms (qf_lira): its argument is linear.
                _linear_term(graph, graph.arguments(atom)[0], Fraction(1), {})
                continue
            _atom_constraint(graph, atom)
        return
    if parameters[0] == "nla":
        # A lemma of Z3's nonlinear solver: bounds and equalities over Int
        # terms with products, no premises. The exporter kept nothing of the
        # hint's polynomial refutation; one is searched for again over the
        # literals (products of two of the facts they deny, the squares of
        # the atoms, and a linear combination, checked in exact arithmetic),
        # and a lemma without one is rejected: Lean has no other proof of it.
        if premises or not literals or _lemma_numeric(graph, node) != "Int":
            raise ReconstructionError("nla th-lemma must be a clause over Int terms without premises at node %d"
                                      % node)
        for literal in literals:
            _linear_constraint(graph, literal)
        if _polynomial_certificate(graph, node) is None:
            raise ReconstructionError("nla th-lemma without a polynomial refutation of its literals at node %d"
                                      % node)
        return
    if parameters[0] not in _COEFFICIENT_HINTS:
        return
    coefficients = [Fraction(parameter) for parameter in parameters[1:]]
    numeric = _lemma_numeric(graph, node)
    if parameters[0] == "cut" or (parameters[0] in ("farkas", "bound") and numeric in ("Int", _CAST)
                                  and not coefficients):
        # An integer cut or gcd conflict, or an integer Farkas or bound step
        # whose LP explanation rested on cuts or on the integer lattice
        # (the legacy core labels a lattice conflict farkas with coefficients
        # that do not re-derive, or unsupported when its own check fails):
        # the exporter kept no coefficients because none certify the
        # rounding, so only the shape is checked (integer linear atoms, held
        # premises included) and Lean proves the clause or the implication.
        # (A coefficient-free farkas or bound over Real falls through to the
        # coefficient count check below.) Through to_real the same holds
        # for the integer lattice of the Int terms (_CAST): a cut there
        # rounds Int atoms, Real atoms over Int terms alone (their linear
        # forms are integer, see _integrality_fact), and the floors of Real
        # terms (to_int, whose integrality the projection onto the Int atoms
        # shows, see _projection_facts), so some literal must reach an Int
        # atom.
        if parameters[0] == "cut" and (numeric not in ("Int", _CAST) or coefficients or premises):
            raise ReconstructionError("cut th-lemma requires an Int certificate or a to_real step, no premises, "
                                      "and no coefficients at node %d" % node)
        for premise in premises:
            _atom_constraint(graph, premise)
        forms = [_linear_constraint(graph, literal)[1] for literal in literals]
        if parameters[0] == "cut" and numeric == _CAST and not any(
                graph.is_int(atom) for terms in forms for atom in terms):
            raise ReconstructionError("cut th-lemma over Real atoms alone at node %d" % node)
        return
    if parameters[0] == "implied-eq" and premises and not coefficients:
        # The legacy core records none, and implied-eq coefficients are never
        # summed: only the literal shapes are checked below.
        coefficients = [Fraction(1)] * (len(premises) + len(literals))
    if len(coefficients) != len(premises) + len(literals):
        raise ReconstructionError("th-lemma %s has %d coefficients for %d premises and %d clause literals at node %d" % (
            parameters[0], len(coefficients), len(premises), len(literals), node))
    if parameters[0] == "implied-eq":
        if not literals:
            raise ReconstructionError("implied-eq th-lemma must end in an arithmetic equality")
        equality, polarity = literals[-1], True
        while graph.kind(equality) == z3.Z3_OP_NOT:
            equality, polarity = graph.arguments(equality)[0], not polarity
        if (not polarity or graph.kind(equality) != z3.Z3_OP_EQ
                or not graph.is_arith(graph.arguments(equality)[0])):
            raise ReconstructionError("implied-eq th-lemma must end in an arithmetic equality")
        _atom_constraint(graph, equality)
        literals, coefficients = literals[:-1], coefficients[:-1]
    constraints = []
    for coefficient, premise in zip(coefficients, premises):
        relation, terms, constant = _atom_constraint(graph, premise)  # a premise holds
        constraints.append((coefficient, relation, terms, constant))
    for coefficient, literal in zip(coefficients[len(premises):], literals):
        relation, terms, constant = _linear_constraint(graph, literal)  # a clause literal is denied
        constraints.append((coefficient, relation, terms, constant))
    # An integer bound propagation may round the combined bound (Z3's checker
    # recomputes the consequent's multiplier after rounding), which the
    # hint's coefficients alone do not show.
    if parameters[0] != "implied-eq" and not linear_combination_refutes(constraints) and not (
            parameters[0] == "bound" and numeric in ("Int", _CAST) and bound_combination_refutes(constraints)):
        raise ReconstructionError("th-lemma %s coefficients do not refute its literals at node %d" % (
            parameters[0], node))


def _check_triangle_eq(graph, node, premises, literals):
    """A legacy axiom relating a Real equality to inequalities: one equality literal, linear atoms otherwise.

    arith_eq_adapter emits (or (not (= s t)) (<= (- s t) 0)), its >= twin,
    and (or (= s t) (not (<= ...)) (not (>= ...))). Only the shape is
    checked here; grind proves the clause.
    """
    if premises or len(literals) < 2:
        raise ReconstructionError("triangle-eq th-lemma must be a clause without premises at node %d" % node)
    equalities = 0
    for literal in literals:
        atom = literal
        while graph.kind(atom) == z3.Z3_OP_NOT:
            atom = graph.arguments(atom)[0]
        if graph.kind(atom) == z3.Z3_OP_EQ and graph.arguments(atom) and graph.is_arith(graph.arguments(atom)[0]):
            _atom_constraint(graph, atom)
            equalities += 1
        else:
            _linear_constraint(graph, literal)
    if equalities != 1:
        raise ReconstructionError("triangle-eq th-lemma must contain exactly one Real equality at node %d" % node)


def _resolution(graph, terms, node):
    premises = graph.arguments(node)[:-1]
    first, units = premises[0], premises[1:]
    literals = graph.clause(graph.conclusion(first))
    conclusion = graph.clause(graph.conclusion(node))
    # A clause may consist of one literal that is itself a disjunction; when a
    # unit complements that whole formula, or the conclusion equals the single
    # remaining literal, treat the formula as one literal rather than a clause.
    whole = graph.conclusion(first)
    if len(literals) > 1 and any(
            graph.kind(graph.conclusion(unit)) == z3.Z3_OP_NOT
            and terms[graph.arguments(graph.conclusion(unit))[0]] == terms[whole] for unit in units):
        literals = (whole,)
    eliminations, matched_units = {}, set()
    for position, literal in enumerate(literals):
        for unit in units:
            fact = graph.conclusion(unit)
            if graph.kind(fact) == z3.Z3_OP_NOT and terms[graph.arguments(fact)[0]] == terms[literal]:
                eliminations.setdefault(position, (unit, True))
                matched_units.add(unit)
            elif graph.kind(literal) == z3.Z3_OP_NOT and terms[graph.arguments(literal)[0]] == terms[fact]:
                eliminations.setdefault(position, (unit, False))
                matched_units.add(unit)
            elif graph.kind(literal) == z3.Z3_OP_FALSE and graph.kind(fact) == z3.Z3_OP_TRUE:
                # The legacy core's theory axioms (or false l) resolved with
                # the unit true; a false literal needs no unit (see branch).
                matched_units.add(unit)
    if set(units) != matched_units:
        raise ReconstructionError("unit-resolution has an unmatched unit at node %d" % node)
    kept = [pos for pos, lit in enumerate(literals) if pos not in eliminations and graph.kind(lit) != z3.Z3_OP_FALSE]
    # Z3's SAT solver identifies a literal (not (not x)) with x: the gate
    # clause (or (not (= (not p) p)) (not (not p)) p) of an equality between
    # Bool terms (an index equality the array solver creates over Bool
    # indices) resolves to p. A kept (not (not x)) whose x is also kept or
    # concluded (and which is not concluded itself) stands for x, proved by
    # contradiction with x's decidability witness.
    concluded = {terms[lit] for lit in conclusion} | {terms[graph.conclusion(node)]}
    candidates = concluded | {terms[literals[pos]] for pos in kept}
    doubles = {}
    for position in kept:
        literal = literals[position]
        if (graph.kind(literal) == z3.Z3_OP_NOT and graph.kind(graph.arguments(literal)[0]) == z3.Z3_OP_NOT
                and terms[literal] not in concluded):
            inner = graph.arguments(graph.arguments(literal)[0])[0]
            if terms[inner] in candidates:
                doubles[position] = inner
    remaining = {terms[doubles.get(pos, literals[pos])] for pos in kept}
    if len(conclusion) > 1 and remaining == {terms[graph.conclusion(node)]}:
        conclusion = (graph.conclusion(node),)
    positions = {}
    for position, literal in enumerate(conclusion):
        if graph.kind(literal) != z3.Z3_OP_FALSE:
            positions.setdefault(terms[literal], position)
    if remaining != set(positions):
        raise ReconstructionError("incorrect unit-resolution conclusion at node %d" % node)

    def cut(position):
        """Whether the literal at position is eliminated or false, not kept."""
        return position in eliminations or graph.kind(literals[position]) == z3.Z3_OP_FALSE

    def eliminate(subject, position, side):
        """Cut an eliminated or false literal off the left or right of subject.

        A literal (not p) eliminated by a proof of p uses Or.neg_resolve_left
        or Or.neg_resolve_right, which take that proof itself: no
        double-negation lambda per elimination (70,817 of them were 2.6 MB of
        the 32 MB of Lean of QF_IDL DTP_k2_n35_c245_s9)."""
        if position not in eliminations:
            return "(%s.resolve_%s (fun _literal => _literal))" % (subject, side)
        unit, negated_unit = eliminations[position]
        return "(%s.%sresolve_%s _step_%d)" % (subject, "" if negated_unit else "neg_", side, unit)

    def contradiction(position, value):
        """A proof of False from a proof value of an eliminated or false literal."""
        if position in eliminations:
            unit, negated_unit = eliminations[position]
            return "(_step_%d %s)" % (unit, value) if negated_unit else "(%s _step_%d)" % (value, unit)
        return value

    def branch(position, value):
        literal = literals[position]
        if cut(position):
            return "(False.elim %s)" % contradiction(position, value)
        if position in doubles:
            literal = doubles[position]
            value = "(@Decidable.byContradiction %s _df%d %s)" % (_formula(graph, literal), literal, value)
        return _inject(positions[terms[literal]], len(conclusion), value)

    support = set(doubles.values())
    if not literals:
        return "(False.elim _step_%d)" % first, support
    # Eliminated literals are cut off the clause by field notation,
    # `(h.resolve_left n)` (Or.resolve_left), which elaborates inside out from
    # the known type of the clause; only kept literals open an Or.elim case
    # split. One nested Or.elim per literal created metavariables at every
    # level and made a unit resolution over a 260-literal clause take seconds.
    # The last kept literal needs no split when every literal after it is
    # eliminated: `(h.resolve_right n)` (Or.resolve_right) with n refuting
    # that tail. In the QF_IDL DTP refutations most resolutions keep one
    # literal of a two-literal clause.
    last = len(literals) - 1
    kept_before_last = [pos for pos in range(last) if not cut(pos)]
    final = kept_before_last[-1] if kept_before_last and cut(last) else None
    subject, cases = "_step_%d" % first, []
    for position in range(last):
        if cut(position):
            subject = eliminate(subject, position, "left")
        elif position == final:
            if position + 1 == last:
                value = eliminate(subject, last, "right")
            else:
                tail = "_tail"
                for eliminated in range(position + 1, last):
                    tail = eliminate(tail, eliminated, "left")
                value = "(%s.resolve_right (fun _tail => %s))" % (subject, contradiction(last, tail))
            value = branch(position, value)
            return "".join(cases) + value + "))" * len(cases), support
        else:
            cases.append("(Or.elim %s (fun _literal => %s) (fun _tail => " % (subject, branch(position, "_literal")))
            subject = "_tail"
    return "".join(cases) + branch(last, subject) + "))" * len(cases), support


def _lemma(graph, terms, node, hypotheses):
    premise, conclusion = graph.arguments(node)
    if graph.kind(graph.conclusion(premise)) != z3.Z3_OP_FALSE:
        raise ReconstructionError("lemma requires a proof of false at node %d" % node)
    if not hypotheses:
        return "(False.elim _step_%d)" % premise, set()
    if len(hypotheses) == 1:
        hypothesis = hypotheses[0]
        if (graph.kind(conclusion) == z3.Z3_OP_NOT
                and terms[graph.arguments(conclusion)[0]] == terms[hypothesis]):
            return "_step_%d" % premise, set()
        if (graph.kind(hypothesis) == z3.Z3_OP_NOT
                and terms[graph.arguments(hypothesis)[0]] == terms[conclusion]):
            return ("(@Decidable.byContradiction %s _df%d _step_%d)" % (
                _formula(graph, conclusion), conclusion, premise)), {conclusion}

    literals = graph.clause(conclusion)
    arguments, decidable = [], {conclusion}
    # A literal's refutation projects it out of the negated clause, one
    # Or.inr per literal before it, so discharging every literal of a wide
    # clause was quadratic: the 780 hypotheses of a negated 40-term distinct
    # took a 2.7 MB line. Over a wide clause the refutations start from the
    # negated clause's tails, bound every _AND_ELIM_STRIDE literals.
    tails, bindings = {0: "_not_clause"}, []

    def negated_literal(position):
        base = position // _AND_ELIM_STRIDE * _AND_ELIM_STRIDE if len(literals) > _AND_ELIM_STRIDE else 0
        for start in range(_AND_ELIM_STRIDE, base + 1, _AND_ELIM_STRIDE):
            if start not in tails:
                tails[start] = "_not_tail%d" % start
                bindings.append("let %s := %s; " % (tails[start], _reject_disjunct(
                    _AND_ELIM_STRIDE, _AND_ELIM_STRIDE + 1, tails[start - _AND_ELIM_STRIDE])))
        return "(fun _literal => %s %s)" % (tails[base], _inject(position - base, len(literals) - base, "_literal"))

    # The first literal discharging each hypothesis: the literal itself
    # negated, or the negation of a negated literal.
    positives, negatives = {}, {}
    for position, literal in enumerate(literals):
        positives.setdefault(terms[literal], position)
        if graph.kind(literal) == z3.Z3_OP_NOT:
            negatives.setdefault(terms[graph.arguments(literal)[0]], position)
    for hypothesis in hypotheses:
        positive = (positives.get(terms[graph.arguments(hypothesis)[0]])
                    if graph.kind(hypothesis) == z3.Z3_OP_NOT else None)
        negative = negatives.get(terms[hypothesis])
        if positive is None and negative is None:
            raise ReconstructionError("lemma does not discharge every hypothesis at node %d" % node)
        if negative is None or (positive is not None and positive <= negative):
            arguments.append(negated_literal(positive))
        else:
            arguments.append("(@Decidable.byContradiction %s _df%d %s)" % (
                _formula(graph, hypothesis), hypothesis, negated_literal(negative)))
            decidable.add(hypothesis)
    contradiction = "%s(_step_%d %s)" % ("".join(bindings), premise, " ".join(arguments))
    return ("(@Decidable.byContradiction %s _df%d (fun _not_clause => %s))" % (
        _formula(graph, conclusion), conclusion, contradiction)), decidable


def _outline_weight(graph, node):
    """The steps a proof step counts as in an outlined lemma: its width when wide, else one.

    The width is a lemma's number of clause literals (one refutation per
    discharged hypothesis) or another step's number of premises. A step of
    hundreds of them elaborated about ten times slower among the let-bound
    steps of a full chunk than alone: the lemma discharging the 780
    hypotheses of a negated 40-term distinct took 14 s inside a 500-step
    chunk, 1.6 s as a lemma of its own. Counted by width, it is cut from the
    chunk around it.
    """
    if graph.kind(node) == z3.Z3_OP_PR_LEMMA:
        width = len(graph.clause(graph.conclusion(node)))
    else:
        width = len(graph.arguments(node)) - 1
    return width if width > _OUTLINE_WIDE_STEP else 1


def _direct_hypotheses(graph, terms):
    """Return the hypothesis steps that their consumers name by the hypothesis itself.

    A hypothesis step proves its formula from the binder `_hypN`, which every
    step depending on it already has in scope. Bound as a step of its own it
    was a function of that binder: each consumer re-applied it, and, used by
    several steps, it became an outlined lemma `fun _hypN => _hypN` imported
    by every lemma using it. In the QF_IDL DTP_k2_n35 refutation this was
    3.3 MB of 36.9 MB of Lean. Only the premise of a `lemma` keeps its step:
    the lemma discharges the hypotheses its premise depends on, so the
    binder is not in scope there. (No conjunction tails start from a
    hypothesis: _and_elim projects a premise under hypotheses from its start.)
    """
    kept = {graph.arguments(node)[0] for node in terms if graph.kind(node) == z3.Z3_OP_PR_LEMMA}
    return {node for node in terms if graph.kind(node) == z3.Z3_OP_PR_HYPOTHESIS and node not in kept}


def _reference_hypotheses(terms, direct):
    """Return the step terms without the direct hypothesis steps, which the others name by their binder."""
    reference = {"_step_%d" % node: terms[node] for node in direct}

    def name(match):
        return reference.get(match.group(0), match.group(0))

    return {node: re.sub(r"\b_step_\d+\b", name, term) for node, term in terms.items() if node not in direct}


def _outline_boundaries(graph, direct=frozenset()):
    """Return the steps checked as separate lemmas: shared subproofs and chunk ends.

    A subproof used by several steps is checked once. A long chain without
    sharing is cut whenever a step would otherwise nest more than
    _OUTLINE_CHUNK_STEPS steps, so each lemma stays within the elaborator's
    default heartbeat budget. A step counts as _outline_weight steps: a step
    wider than _OUTLINE_WIDE_STEP counts its width, so it is cut from the
    chain around it, and its hypothesis premises stay inline as its binders
    rather than being cut. Only steps the root uses are outlined; the log
    may record derivations the refutation never needs. Arguments precede
    their node, so one increasing pass sees every premise's final size before
    its consumer. The direct hypothesis steps (_direct_hypotheses) are not
    bound as steps and are never outlined.
    """
    reachable, pending = set(), [graph.proof]
    while pending:
        node = pending.pop()
        if node not in reachable:
            reachable.add(node)
            pending.extend(graph.arguments(node)[:-1])
    uses = Counter(premise for node in reachable for premise in graph.arguments(node)[:-1])
    boundaries = {node for node in reachable if uses[node] > 1 and node not in direct} | {graph.proof}
    size = {}
    for node in sorted(reachable):
        total = weight = _outline_weight(graph, node)
        for premise in graph.arguments(node)[:-1]:
            if premise in boundaries or premise in direct:
                continue
            if weight > 1 and graph.kind(premise) == z3.Z3_OP_PR_HYPOTHESIS:
                # The hundreds of hypotheses of a wide step stay its binders:
                # outlined, each would be a lemma with nothing to check.
                total += 1
            elif total + size[premise] > _OUTLINE_CHUNK_STEPS:
                boundaries.add(premise)  # used once: nothing else counted it
            else:
                total += size[premise]
        size[node] = total
    return boundaries


def _witness_key(name):
    """Order decidability witnesses: atoms (_dN) before formulas (_dfN), by node."""
    formula = name.startswith("_df")
    return (formula, int(name[3 if formula else 2:]))


def _witness_formula(graph, name):
    return _formula(graph, int(name[3:])) if name.startswith("_df") else "(_atoms %d)" % int(name[2:])


# A unit resolution that keeps one literal is the clause's proof with every
# other literal cut off by field notation, `(_step_N.resolve_left u)` and so on
# (_resolution): Or.resolve_* infer its type from the clause's, the kept
# literal's formula, so the let binding it states no type. Any other term
# (an Or.inl/Or.inr injection into a wider conclusion, a case split, a proof by
# contradiction, False.elim) starts otherwise and keeps the stated type. In
# the QF_IDL DTP_k2_n35_c245_s9 refutation 46,002 of the 49,550 steps bound
# inside others were such resolutions.
_INFERRED_TYPE = re.compile(r"\(+_(?:step_|hyp)\d+\.(?:neg_)?resolve_(?:left|right) ")


def _step_blocks(graph, terms, dependencies, excluded):
    """Return the let-binding lines of each proof step bound at the top level of its proof.

    A step under hypotheses is a function of them, so each step consuming
    it re-applies it, and its binders restate every hypothesis formula: in
    the QF_IDL DTP_k2_n35 refutation (61,000 unit resolutions under 639
    hypotheses) this was 28 of the 54 MB of proof-step text. A step under
    hypotheses that one other step uses, whose hypotheses that step also
    has, is bound inside that step instead, where its hypotheses are already
    in scope: no binders and no re-application. Steps in excluded (outlined
    lemmas, premises of conjunction tails) stay at the top level, and
    nesting stops at _NESTED_STEP_DEPTH levels, so no let value nests more
    than that many others. A premise without a term (a direct hypothesis,
    see _direct_hypotheses) is not bound as a step: its consumers name its
    binder.
    """
    uses = Counter(premise for node in terms for premise in graph.arguments(node)[:-1])
    inner, depth = {}, {}
    for node in sorted(terms):
        inner[node], depth[node] = [], 0
        if graph.kind(node) == z3.Z3_OP_PR_LEMMA:
            continue  # its premise depends on the hypotheses it discharges
        for premise in dict.fromkeys(graph.arguments(node)[:-1]):
            if (premise in terms and uses[premise] == 1 and dependencies[premise] and premise not in excluded
                    and set(dependencies[premise]) <= set(dependencies[node])
                    and depth[premise] < _NESTED_STEP_DEPTH):
                inner[node].append(premise)
                depth[node] = max(depth[node], depth[premise] + 1)
    nested = {premise for premises in inner.values() for premise in premises}

    def block(node, indent):
        parameters = "" if node in nested else "".join(
            " (_hyp%d : %s)" % (hypothesis, _formula(graph, hypothesis)) for hypothesis in dependencies[node])
        result = "" if _INFERRED_TYPE.match(terms[node]) else " : %s" % _formula(graph, graph.conclusion(node))
        lines = ["%slet _step_%d%s%s :=" % (indent, node, parameters, result)]
        for premise in inner[node]:
            lines.extend(block(premise, "    "))
        if graph.kind(node) != z3.Z3_OP_PR_LEMMA:
            for premise in dict.fromkeys(graph.arguments(node)[:-1]):
                if premise in terms and dependencies[premise] and premise not in inner[node]:
                    arguments = "".join(" _hyp%d" % hypothesis for hypothesis in dependencies[premise])
                    lines.append("    let _step_%d := _step_%d%s" % (premise, premise, arguments))
        lines.append("    " + terms[node])
        return lines

    return {node: block(node, "  ") for node in sorted(terms) if node not in nested}


_CLASSICAL_CONTRADICTION = "classical_by_contradiction"
# Decidable.byContradiction at the witness Classical.propDecidable, which the
# classical lemmas bound by a let before: the same axiom (Classical.choice),
# where Classical.byContradiction would add propext and Quot.sound.
_CLASSICAL_CONTRADICTION_LEMMA = [
    "",
    "private theorem %s {p : Prop} (h : Not p -> False) : p :=" % _CLASSICAL_CONTRADICTION,
    "  @Decidable.byContradiction p (Classical.propDecidable p) h",
]


def _classical_contradictions(graph, lines):
    """Return the lines with each proof by contradiction over a classical witness by the lemma above.

    `(@Decidable.byContradiction F _dfN h)` names F and a witness `_dfN`
    that the lemma binds by `let _dfN := Classical.propDecidable F`; the
    helper takes F from the expected type or from h. In the QF_IDL
    DTP_k2_n35 refutation these heads and lets were 1.9 MB of 27.7 MB.
    A witness used otherwise (as an instance argument) keeps its let.
    """
    text = "\n".join(lines)
    for formula in sorted({int(name) for name in re.findall(r"\b_df(\d+)\b", text)}):
        head = "@Decidable.byContradiction %s _df%d" % (_formula(graph, formula), formula)
        text = re.sub(re.escape(head) + r"\b", _CLASSICAL_CONTRADICTION, text)
    return text.split("\n") if lines else lines


def _import_value(node, classical, witnesses):
    """The application of an outlined lemma that imports it into another."""
    return "proof_step_%d _inputs%s" % (node, "" if classical else "".join(" " + name for name in witnesses[node]))


def _merge_single_imports(graph, dependencies, local, external, needed, body, conclusion, classical, witnesses):
    """Return the lemmas an outlined lemma imports by a let, and its body and conclusion lines.

    A lemma used once in the lemma importing it is applied at that use,
    without a let of its own: one under hypotheses in the line that
    re-applies it to them (`let _step_N := proof_step_N _inputs _hyp...`),
    one without them in place of its name. In the QF_IDL DTP_k2_n35
    refutation 92,491 of the 100,549 imports were used once; applying them
    in place cut its Lean from 30.5 to 27.7 MB. A lemma whose conjunction tails are
    bound, or which a `lemma` step uses (applying it to the proofs of the
    hypotheses that step discharges, without a re-application), keeps its
    let, as does any lemma whose single use is not found where expected.
    """
    consumers = {node: set() for node in external}
    for node in local:
        for premise in graph.arguments(node)[:-1]:
            if premise in consumers:
                consumers[premise].add(node)
    single = {node for node in external
              if len(consumers[node]) == 1 and not needed.get(node, 0)
              and all(graph.kind(consumer) != z3.Z3_OP_PR_LEMMA for consumer in consumers[node])}
    text = "\n".join(body + conclusion)
    occurrences = Counter(int(name[6:]) for name in re.findall(r"\b_step_\d+\b", text))
    reapplied = Counter(int(match) for match in re.findall(r"^ *let _step_(\d+) := _step_\1(?: _hyp\d+)+$", text, re.M))
    merged = {node for node in single if (reapplied[node] == 1 if dependencies[node]
                                          else occurrences[node] == 1 and not reapplied[node])}

    def application(match):
        node = int(match.group(3))
        if node not in merged:
            return match.group(0)
        return "%slet _step_%d := %s%s" % (match.group(1), node, _import_value(node, classical, witnesses),
                                           match.group(4))

    def use(match):
        node = int(match.group(0)[6:])
        if node not in merged or dependencies[node]:
            return match.group(0)
        return "(%s)" % _import_value(node, classical, witnesses)

    def merge(lines):
        text = re.sub(r"^( *)let (_step_(\d+)) := \2((?: _hyp\d+)+)$", application, "\n".join(lines), flags=re.M)
        return re.sub(r"\b_step_\d+\b", use, text).split("\n") if lines else lines

    if merged:
        body, conclusion = merge(body), merge(conclusion)
    return [node for node in sorted(external) if node not in merged], body, conclusion


# A step's application to its hypotheses inside the step using it: the
# re-application of a step bound at the top level (`let _step_N := _step_N
# _hyp...`) or of an imported lemma (`let _step_N := proof_step_N _inputs
# _hyp...`, decidability witnesses before the hypotheses in the propositional
# slice). Its arguments are hypotheses and witnesses only, never another
# step, so no application substituted here names a step pending beside it.
_REAPPLICATION = re.compile(r"^ *let (_step_\d+) := ((?:proof_step_\d+ _inputs|_step_\d+)(?: _(?:hyp|df?)\d+)+)$")


def _reapplications_in_place(lines):
    """Return the lines with each re-application used once by the term after it applied there instead.

    _step_blocks writes a step's re-applications of its premises after the
    steps nested in it, directly before its term: the next line that is not
    a re-application is the term using them, and the let's whole scope. A
    name that term uses once is replaced by the application itself, the
    others keep their let. In the QF_IDL DTP_k2_n35_c245_s9 refutation these
    were 49,236 lets.
    """
    result, pending = [], []
    for line in lines:
        match = _REAPPLICATION.match(line)
        if match:
            pending.append(match)
            continue
        kept = pending
        if pending and not line.lstrip().startswith("let "):
            kept = []
            for match in pending:
                pattern = r"\b%s\b" % match.group(1)
                if len(re.findall(pattern, line)) == 1:
                    line = re.sub(pattern, lambda _use, value=match.group(2): "(%s)" % value, line)
                else:
                    kept.append(match)
        result.extend(match.group(0) for match in kept)
        result.append(line)
        pending = []
    result.extend(match.group(0) for match in pending)
    return result


def _outline_steps(graph, steps, dependencies, signature, tails, boundaries):
    """Check proof subgraphs separately instead of one enormous nested term.

    Returns the Lean lines and the decidability witnesses the root lemma takes
    as parameters. The arithmetic and uninterpreted slices already report the
    standard axioms, so their lemmas take classical witnesses locally; the
    propositional slice stays axiom-free by receiving every witness as a
    parameter that the main theorem introduces constructively. Each lemma
    binds the conjunction tails its and-elims start from (tails, see
    _and_elim) after the premise they project. A step bound inside another
    (_step_blocks) is part of that step's lines.
    """
    classical = bool(graph.arithmetic or graph.uninterpreted)
    inputs = _balanced("And", [_formula(graph, node) for node in graph.assertions], "True")
    lines = ["", "private def Inputs %s : Prop := %s" % (signature, inputs)]
    # The interpretation is implicit in each lemma, determined by the type of
    # _inputs: a lemma is imported as `proof_step_N _inputs`.
    implicit = re.sub(r"\((_\w+ : [^()]*)\)", r"{\1}", signature)
    if "(" in implicit:
        # A binder whose type has parentheses would stay explicit, and every
        # `proof_step_N _inputs` import would be ill-typed.
        raise ReconstructionError("cannot make the interpretation implicit: %s" % signature)
    witnesses = {}
    for root in sorted(boundaries):
        local, external, pending = set(), set(), [root]
        while pending:
            node = pending.pop()
            if node != root and node in boundaries:
                external.add(node)
            elif node not in local:
                local.add(node)
                pending.extend(graph.arguments(node)[:-1])
        needed = _needed_tails(tails, local)
        # Every other local step precedes the root (arguments precede their
        # node), and no and-elim of this lemma starts from the root's tails.
        body = [line for node in sorted(local) if node in steps and node != root
                for line in steps[node] + _tail_lets(node, needed.get(node, 0))]
        # The root is the lemma's statement: its hypotheses are the binders
        # of a fun, the statement's premises, not restated. Without
        # hypotheses its lines move to the lemma's column, so that none
        # continues the application bound on the line before it.
        if dependencies[root]:
            conclusion = ["  fun%s =>" % "".join(" _hyp%d" % hypothesis for hypothesis in dependencies[root])]
            conclusion.extend(steps[root][1:])
        else:
            conclusion = [line[2:] for line in steps[root][1:]]
        imports, body, conclusion = _merge_single_imports(graph, dependencies, local, external, needed,
                                                          body, conclusion, classical, witnesses)
        body, conclusion = _reapplications_in_place(body), _reapplications_in_place(conclusion)
        if classical:
            body, conclusion = _classical_contradictions(graph, body), _classical_contradictions(graph, conclusion)
        decidable = set(re.findall(r"\b_df?\d+\b", "\n".join(body + conclusion)))
        if not classical:
            for node in external:
                decidable.update(witnesses[node])
        witnesses[root] = sorted(decidable, key=_witness_key)
        result = _formula(graph, graph.conclusion(root))
        for hypothesis in reversed(dependencies[root]):
            result = "(%s -> %s)" % (_formula(graph, hypothesis), result)
        lines.extend([
            "",
            "private theorem proof_step_%d %s" % (root, implicit),
            "    (_inputs : Inputs _atoms%s)" % graph.valuation,
        ])
        if classical:
            lines.append("    : %s :=" % result)
            for name in witnesses[root]:
                lines.append("  let %s := Classical.propDecidable %s" % (name, _witness_formula(graph, name)))
        else:
            lines.extend("    (%s : Decidable %s)" % (name, _witness_formula(graph, name))
                         for name in witnesses[root])
            lines.append("    : %s :=" % result)
        for node in imports:
            lines.append("  let _step_%d := %s" % (node, _import_value(node, classical, witnesses)))
            lines.extend(_tail_lets(node, needed.get(node, 0)))
        lines.extend(body)
        lines.extend(conclusion)
    if classical and any(_CLASSICAL_CONTRADICTION in line for line in lines):
        lines[2:2] = _CLASSICAL_CONTRADICTION_LEMMA
    return lines, ([] if classical else witnesses[graph.proof])


def reconstruct(source, certificate):
    """Return Lean source; callers must check it before claiming verification."""
    graph = _validate_graph(source, certificate)
    terms, tables = _bind_input(source, graph, certificate["fragment"], certificate["query"])
    _, query, queries = query_snapshot(source, certificate["query"])
    # Each symbol table is numbered from zero; a declaration belongs to one table,
    # so the Boolean-valued and term-valued tables can share one index map each.
    indices = {table: {decl: index for index, decl in enumerate(sorted(symbols.values()))}
               for table, symbols in tables.items()}
    atom_indices = {**indices["atoms"], **indices["predicates"]}
    variable_indices = {**indices["variables"], **indices["elements"], **indices["functions"],
                        **indices["numeric_functions"], **indices["arrays"], **indices["array_functions"]}
    for declaration, decl in enumerate(graph.declarations):
        symbol = _map_symbol(graph, declaration)
        if symbol is not None:
            # The family of the mapped function by its element result sort,
            # and its index in the table _bind_input entered it in.
            name, domain, range_name = symbol
            table = _symbol_table(range_name, len(domain), graph.sorts)
            family = ("_m.preds" if table == "predicates" else _NUMERIC_FUNCTIONS[range_name]
                      if table == "numeric_functions" else _sort_family(graph, range_name, "funs"))
            graph.map_heads[declaration] = "%s %d" % (family, indices[table][tables[table][name]])
    defaults = _generic_defaults(graph)
    digest = hashlib.sha256(source.encode("utf-8")).hexdigest()
    namespace = "Z3Proofs.NativeCertificate.p" + digest
    lines = ["import Init", "", "-- Original input SHA-256: " + digest]
    if queries > 1:
        # The theorem is about one query of an incremental script: the
        # assertions in scope at that check-sat, with its assumptions.
        lines.append("-- Certified query: check-sat %d of %d (zero-based index %d); the assertions below are "
                     "the ones in scope there, assumptions included." % (query + 1, queries, query))
    for table, label in _TABLE_LABELS.items():
        for name, decl in sorted(tables[table].items(), key=lambda item: indices[table][item[1]]):
            shown = label % _symbol_signature(graph, decl)[1] if table == "numeric_functions" else label
            lines.append("-- %s %d: %s" % (shown, indices[table][decl], json.dumps(name, ensure_ascii=True)))
    if graph.arithmetic and graph.numeric == "Int":
        lines.append("-- Int variables are encoded as Int; the integer lemmas are proved by omega, else grind.")
    elif graph.numeric == _MIXED:
        kinds = {decl.kind for decl in graph.declarations}
        conversions = "to_real is Int.cast into Rat" if z3.Z3_OP_TO_REAL in kinds else ""
        if kinds & {z3.Z3_OP_TO_INT, z3.Z3_OP_IS_INT}:
            conversions += (", " if conversions else "") + "to_int is Rat.floor"
        lines.append("-- Real variables are encoded as Rat (_vars) and Int variables as Int (_ivars), %s; "
                     "the integer lemmas are proved by omega, else grind." % (
                         conversions or "no term converting between them"))
    elif graph.arithmetic:
        lines.append("-- Real variables are encoded as Rat; see the exporter documentation.")
    if any(decl.kind in _INT_NAMES and decl.range == "Int" for decl in graph.declarations):
        lines.append("-- Int div and mod by a numeral are Lean's Euclidean / and %; abs is the ite SMT-LIB defines.")
    quotients = {node for node in range(len(graph.nodes)) if graph.is_term(node) and _negative_quotient(graph, node)}
    if quotients:
        lines.append("-- Int div by a negative constant d is written 0 - t / (0 - d), which is t / d: "
                     "see the theorem term_N_quotient after each such definition.")
    if any(decl.kind == z3.Z3_OP_REM for decl in graph.declarations):
        lines.append("-- Int rem by a numeral k is Z3's (ite (>= k 0) (mod t k) (- (mod t k))): "
                     "t % k, or 0 - t % k for k < 0.")
    if any(graph.is_term(node) and graph.kind(node) in (z3.Z3_OP_UMINUS, z3.Z3_OP_ABS)
           and _negated_as_difference(graph, graph.arguments(node)[0]) for node in range(len(graph.nodes))):
        lines.append("-- The negation of an Int term t is written 0 - t, of a positive numeral -k.")
    if any(decl.kind in _PSEUDO_BOOLEAN for decl in graph.declarations):
        lines.append("-- Pseudo-Boolean constraints compare the weighted sum of their literals' 0/1 values over Int "
                     "with their bound.")
    if any(decl.kind in _NUMERIC_KINDS and decl.range == "Real" for decl in graph.declarations):
        lines.append("-- Real abs, which Z3 accepts beyond SMT-LIB, is the ite (if t >= 0 then t else -t).")
    if graph.arithmetic and graph.uninterpreted:
        for sort in _ARITH_SORTS if graph.numeric == _MIXED else (graph.numeric,):
            lines.append("-- %s arguments of functions and predicates are injected into _m.U by %s;"
                         " functions with %s result are the family %s." % (
                             sort, _INJECTIONS[sort], {"Real": "a Real", "Int": "an Int"}[sort],
                             _NUMERIC_FUNCTIONS[sort]))
    pointwise = _pointwise_indices(graph)
    for sort in graph.index_sorts:
        # Maps, set operators, subsets, or constant arrays are over arrays
        # indexed by it, so their index type is exactly the sort (_index_sorts).
        reasons = [reason for reason, indices in (("pointwise maps", pointwise),
                                                  ("constant arrays", graph.constant_indices)) if sort in indices]
        lines.append("-- Uninterpreted sort %s is the type %s of its own, the index type of the %s: "
                     "constants %s, functions %s, arguments of functions and predicates injected into _m.U by %s." % (
                         json.dumps(sort, ensure_ascii=True), _component_type(graph, sort), " and ".join(reasons),
                         _sort_family(graph, sort, "elems"), _sort_family(graph, sort, "funs"),
                         _sort_family(graph, sort, "inj")))
    plain = [sort for sort in graph.carriers if sort not in graph.enumerations and sort not in graph.index_sorts]
    if len(plain) == 1:
        lines.append("-- Uninterpreted sort %s is the type _m.U; functions and predicates take argument lists."
                     % json.dumps(plain[0], ensure_ascii=True))
    elif plain:
        # One carrier for every sort is sound: a many-sorted model is an instance
        # of the theorem over the disjoint union of its carriers.
        lines.append("-- Uninterpreted sorts %s are the one type _m.U; functions and predicates take argument lists."
                     % ", ".join(json.dumps(sort, ensure_ascii=True) for sort in plain))
    elif graph.uninterpreted and not graph.arrays and not graph.enumerations:
        lines.append("-- No uninterpreted sort: the type _m.U carries only the Boolean arguments of the predicates.")
    elif graph.uninterpreted and not graph.enumerations:
        lines.append("-- No %suninterpreted sort: the type _m.U carries only the arguments of the functions, if any."
                     % ("other " if graph.index_sorts else ""))
    for sort in sorted(graph.enumerations):
        first = graph.constructor_index(graph.enumerations[sort][0], sort)
        arrays = any(_array_components(array)[1] == sort for array in graph.arrays)
        lines.append("-- Enumeration %s is part of _m.U with constructors %s, _m.ctors %d to %d (enum_distinct, "
                     "enum_cases_*, enum_fcases_*%s)." % (
                         json.dumps(sort, ensure_ascii=True),
                         ", ".join(json.dumps(name, ensure_ascii=True) for name in graph.enumerations[sort]),
                         first, first + len(graph.enumerations[sort]) - 1,
                         ", enum_acases_*, enum_afcases_* of its arrays" if arrays else ""))
    if graph.arrays:
        # An array sort's uninterpreted index and element sorts are
        # carriers, so the sentence above names them; Int and Real ones are
        # Int and Rat.
        lines.append("-- Array sorts %s are functions %s; select is _select, store the classical update _store, and "
                     "the extensionality witness array-ext is _array_diff." % (
                         ", ".join(json.dumps(sort, ensure_ascii=True) for sort in graph.arrays),
                         ", ".join("%s -> %s (_m.%s)" % (_array_types(graph, sort) + (_array_family(graph, sort),))
                                   for sort in graph.arrays)))
    if graph.generic:
        lines.append("-- The array solver's default values (the input names none) are the arrays' values at one "
                     "index that no store writes: %s." % ", ".join(
                         "%s over %s" % (_generic_index(sort), sort) for sort in graph.generic))
    if tables["array_functions"]:
        families = sorted({_array_functions(graph, graph.declarations[decl].range)
                           for decl in tables["array_functions"].values()})
        lines.append("-- Functions into array sorts are the families %s, one per Lean array type." % ", ".join(
            "_m." + family for family in families))
    if any(decl.kind == z3.Z3_OP_UNINTERPRETED and "Bool" in decl.domain for decl in graph.declarations):
        lines.append("-- Boolean arguments of functions and predicates are injected into _m.U by _m.bool.")
    # Formulas over wide n-ary connectives render as right-nested And/Or chains
    # and long refutations nest hundreds of let-bound steps; every declaration
    # (definitions, lemmas, proof steps, the theorem) elaborates under a raised
    # recursion limit, scoped to this namespace. This is not a trust setting.
    lines.extend(["namespace " + namespace, "", "set_option maxRecDepth 100000", ""])
    options = len(lines) - 1
    lines.extend(_interpretation_structure(graph, tables, variable_indices))
    if graph.arrays:
        lines.extend(_ARRAY_DEFINITIONS + [""])
        if any(_enumeration_array(graph, sort) for sort in graph.arrays):
            lines.extend(_ENUMERATION_ARRAY_DEFINITIONS + [""])
    if any(decl.kind in (z3.Z3_OP_CONST_ARRAY, z3.Z3_OP_ARRAY_DEFAULT) for decl in graph.declarations):
        lines.extend(_constant_array_definitions(graph) + [""])
        if any(_enumeration_array(graph, sort) for sort in graph.arrays):
            lines.extend(_ENUMERATION_CONSTANT_DEFINITIONS + [""])
            if not graph.generic:
                lines.extend(_ENUMERATION_DEFAULT_DEFINITIONS + [""])
    if graph.subset_rewrite or any(decl.kind == z3.Z3_OP_ARRAY_MAP or decl.kind in _SET_OPERATOR_NAMES
                                   for decl in graph.declarations):
        lines.extend(_SET_DEFINITIONS + [""])
    if any(decl.kind == z3.Z3_OP_SET_SUBSET for decl in graph.declarations):
        lines.extend(_SUBSET_DEFINITION + [""])
        if graph.subset_rewrite:
            lines.extend(_SUBSET_REWRITE + [""])
    if any(decl.kind in _CONVERSION_KINDS for decl in graph.declarations):
        lines.extend(_CAST_LEMMAS + [""])
    if graph.floors:
        lines.extend(_FLOOR_VALUE_LEMMA + [""])
    if quotients:
        lines.extend(_NEGATIVE_QUOTIENT_LEMMA + [""])
    if any(decl.kind in _PSEUDO_BOOLEAN for decl in graph.declarations):
        lines.extend(_PSEUDO_BOOLEAN_LEMMAS + [""])
    if any(_boolean_distinct(graph, node) for node in range(len(graph.nodes))):
        lines.extend(_BOOLEAN_DISTINCT_LEMMA + [""])
    signature = "(_atoms : Nat -> Prop)" + _valuation_binder(graph)
    classical = set()  # Term nodes containing an ite or abs: their classical instance is noncomputable.
    # With the default values read at a generic index, the definitions that
    # mention one are written after the index, which is defined over the
    # others (the index terms of the stores among them).
    late = []
    for node in range(len(graph.nodes)):
        definitions = late if graph.generic and node in defaults else lines
        if graph.is_term(node):
            if graph.kind(node) in (z3.Z3_OP_ITE, z3.Z3_OP_ABS, z3.Z3_OP_STORE, z3.Z3_OP_ARRAY_EXT,
                                    z3.Z3_OP_ARRAY_DEFAULT) or any(
                    arg in classical for arg in graph.arguments(node)) or (
                    graph.kind(node) == z3.Z3_OP_ARRAY_MAP and graph.decl(node).parameters[0] == "ite"):
                classical.add(node)
            definitions.append("%sdef term_%d %s : %s := %s" % (
                "noncomputable " if node in classical else "", node, signature,
                graph.lean_type(node), _term_body(graph, node, variable_indices)))
            if node in quotients:
                definitions.append(_quotient_theorem(graph, node, signature))
        elif graph.decl(node).range == "Bool":
            definitions.append("def formula_%d %s : Prop := %s" % (
                node, signature, _formula_body(graph, node, atom_indices)))
    if graph.generic:
        lines.extend(_generic_index_definitions(graph, signature) + late)
    rewrites, def_axioms, th_lemmas, decidable_atoms, decidable_formulas = {}, {}, {}, set(), set()
    for node in range(len(graph.nodes)):
        if graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA:
            _check_th_lemma(graph, node)
            if graph.decl(node).parameters[0] == "cnf":
                lemma, term = _cnf_lemma(graph, node, atom_indices, variable_indices)
            elif graph.decl(node).parameters[0] == "pb":
                lemma, term = _pseudo_boolean_lemma(graph, node, "th_lemma", atom_indices)
            else:
                lemma, term = _grind_lemma(graph, node, "th_lemma", atom_indices, variable_indices,
                                           opaque_tactic=_opaque_tactic(graph, node),
                                           structural=(_farkas_combination(graph, node)
                                                       or _product_combination(graph, node)
                                                       or _split_combination(graph, node)))
            lines.extend(lemma)
            th_lemmas[node] = term
        elif graph.kind(node) == z3.Z3_OP_PR_REWRITE:
            lemma, support, term = _rewrite_lemma(graph, node, atom_indices, variable_indices, terms)
            lines.extend(lemma)
            decidable_atoms.update(support)
            rewrites[node] = term
        elif graph.kind(node) == z3.Z3_OP_PR_DEF_AXIOM:
            lemma, support, term = _def_axiom_lemma(graph, terms, node)
            lines.extend(lemma)
            decidable_formulas.update(support)
            def_axioms[node] = term
    assumptions = {}
    for position, assertion in enumerate(graph.assertions):
        assumptions.setdefault(terms[assertion], position)
    outline = sum(graph.decl(n).range == "Proof" for n in range(len(graph.nodes))) > _OUTLINE_PROOF_STEPS
    step_terms = {}
    tails = {}  # and-elim node -> the (premise, operand) tail it projects from
    hypothesis_formulas, dependencies = {}, {}
    ite_congruence = False
    for node in range(len(graph.nodes)):
        if graph.decl(node).range != "Proof":
            continue
        conclusion = graph.conclusion(node)
        premises = graph.arguments(node)[:-1]
        dependencies[node] = tuple(sorted({
            hypothesis for premise in premises for hypothesis in dependencies[premise]
        }))
        if graph.kind(node) == z3.Z3_OP_PR_ASSERTED:
            if terms[conclusion] not in assumptions:
                raise ReconstructionError("asserted node %d is not an original assertion" % node)
            position = assumptions[terms[conclusion]]
            term = (_balanced_select(position, len(graph.assertions), "_inputs") if outline else "_h%d" % position)
        elif graph.kind(node) == z3.Z3_OP_PR_HYPOTHESIS:
            hypothesis = hypothesis_formulas.setdefault(terms[conclusion], conclusion)
            dependencies[node] = (hypothesis,)
            term = "_hyp%d" % hypothesis
        elif graph.kind(node) == z3.Z3_OP_PR_TRUE:
            if graph.kind(conclusion) != z3.Z3_OP_TRUE:
                raise ReconstructionError("true-axiom must conclude true at node %d" % node)
            term = "True.intro"
        elif graph.kind(node) == z3.Z3_OP_PR_LEMMA:
            term, support = _lemma(graph, terms, node, dependencies[node])
            decidable_formulas.update(support)
            dependencies[node] = ()
        elif graph.kind(node) == z3.Z3_OP_PR_MODUS_PONENS:
            term = _modus_ponens(graph, terms, node)
        elif graph.kind(node) == z3.Z3_OP_PR_REWRITE:
            term = rewrites[node]
        elif graph.kind(node) == z3.Z3_OP_PR_DEF_AXIOM:
            term = def_axioms[node]
        elif graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA:
            term = th_lemmas[node]
        elif graph.kind(node) in (z3.Z3_OP_PR_REFLEXIVITY, z3.Z3_OP_PR_SYMMETRY,
                                 z3.Z3_OP_PR_TRANSITIVITY):
            term = _equivalence_step(graph, terms, node)
        elif graph.kind(node) in (z3.Z3_OP_PR_IFF_TRUE, z3.Z3_OP_PR_IFF_FALSE):
            term = _iff_constant(graph, terms, node)
        elif graph.kind(node) == z3.Z3_OP_PR_TRANSITIVITY_STAR:
            term = _transitivity_star(graph, terms, node)
        elif graph.kind(node) == z3.Z3_OP_PR_MONOTONICITY:
            term, uses_ite, lemma = _monotonicity(graph, terms, node, atom_indices, variable_indices)
            ite_congruence = ite_congruence or uses_ite
            lines.extend(lemma)  # emitted before the theorem, like every other private lemma
        elif graph.kind(node) == z3.Z3_OP_PR_COMMUTATIVITY:
            term = _commutativity(graph, terms, node)
        elif graph.kind(node) == z3.Z3_OP_PR_AND_ELIM:
            term, tail = _and_elim(graph, terms, node, not dependencies[premises[0]])
            if tail is not None:
                tails[node] = tail
        elif graph.kind(node) == z3.Z3_OP_PR_NOT_OR_ELIM:
            term, formula = _not_or_elim(graph, terms, node)
            if formula is not None:
                decidable_formulas.add(formula)
        elif graph.kind(node) == z3.Z3_OP_PR_UNIT_RESOLUTION:
            term, support = _resolution(graph, terms, node)
            decidable_formulas.update(support)
        else:
            raise ReconstructionError("unsupported native proof rule: %s" % graph.decl(node).name)
        step_terms[node] = term
    if dependencies[graph.proof]:
        raise ReconstructionError("the root proof has undischarged hypotheses")
    if ite_congruence:
        lines.extend(_ITE_CONGRUENCE)
    direct = _direct_hypotheses(graph, step_terms)
    step_terms = _reference_hypotheses(step_terms, direct)
    boundaries = _outline_boundaries(graph, direct) if outline else set()
    step_blocks = _step_blocks(graph, step_terms, dependencies, boundaries | {premise for premise, _ in tails.values()})
    witnesses = []
    if outline:
        outlined, witnesses = _outline_steps(graph, step_blocks, dependencies, signature, tails, boundaries)
        lines.extend(outlined)
    if witnesses or (not outline and (decidable_atoms or decidable_formulas)):
        # A continuation ending in False can eliminate the temporary decidability
        # assumptions constructively, preserving the original theorem statement.
        lines.extend([
            "",
            "private theorem refute_with_decidable (p : Prop)",
            "    (k : Decidable p -> False) : False :=",
            "  k (.isFalse (fun hp => k (.isTrue hp)))",
        ])
    lines.extend(["", "theorem unsat " + signature])
    for position, assertion in enumerate(graph.assertions):
        lines.append("    (_h%d : %s)" % (position, _formula(graph, assertion)))
    lines.append("    : False :=")
    if outline:
        for name in witnesses:
            lines.append("  refute_with_decidable %s fun %s =>" % (_witness_formula(graph, name), name))
        inputs = _balanced("And.intro", ["_h%d" % i for i in range(len(graph.assertions))], "True.intro")
        lines.append("  @proof_step_%d _atoms%s %s%s" % (
            graph.proof, graph.valuation, inputs, "".join(" " + name for name in witnesses)))
    else:
        for atom in sorted(decidable_atoms):
            lines.append("  refute_with_decidable (_atoms %d) fun _d%d =>" % (atom, atom))
        for formula in sorted(decidable_formulas):
            lines.append("  refute_with_decidable %s fun _df%d =>" % (_formula(graph, formula), formula))
        needed = _needed_tails(tails, dependencies)
        for node, block in step_blocks.items():
            lines.extend(_reapplications_in_place(block) + _tail_lets(node, needed.get(node, 0)))
        lines.append("  _step_%d" % graph.proof)
    lines.extend(["", "end " + namespace, ""])
    text = "\n".join(lines)
    if len(text) > _SERIAL_ELABORATION_CHARS:
        lines.insert(options, "set_option Elab.async false")
        text = "\n".join(lines)
    return text


def check_and_write(source, certificate, output):
    """Publish a Lean file atomically, only after the pinned checker accepts it."""
    text = reconstruct(source, certificate)
    output = Path(output)
    if output.suffix != ".lean":
        raise ReconstructionError("the output filename must end in .lean")
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", suffix=".lean",
                                         prefix="z3_proof_", dir=output.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(text)
        subprocess.run([str(_CHECK_LEAN), str(temporary)], check=True, capture_output=True, text=True)
        os.replace(temporary, output)
        temporary = None
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="original SMT-LIB input, not taken on trust from the certificate")
    parser.add_argument("certificate", type=Path, help="native JSON proof bundle")
    parser.add_argument("-o", "--output", required=True, type=Path, help="Lean proof file to publish after checking")
    args = parser.parse_args()
    try:
        for original in (args.input, args.certificate):
            if (args.output.resolve() == original.resolve()
                    or (args.output.exists() and original.exists() and args.output.samefile(original))):
                raise ReconstructionError("output must not overwrite the input or certificate")
        with args.input.open(encoding="utf-8", newline="") as stream:
            source = stream.read()
        with args.certificate.open(encoding="utf-8") as stream:
            certificate = load_certificate(stream)
        check_and_write(source, certificate, args.output)
    except subprocess.CalledProcessError as error:
        sys.stderr.write(error.stdout or "")
        sys.stderr.write(error.stderr or "")
        parser.exit(error.returncode if error.returncode > 0 else 1, "Lean checking failed; no proof was published.\n")
    except (ReconstructionError, ProofExportError, z3.Z3Exception, OSError, ValueError) as error:
        parser.exit(2, "%s: error: %s\n" % (parser.prog, error))
    print("Lean checked the refutation; wrote %s" % args.output)


if __name__ == "__main__":
    main()
