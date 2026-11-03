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
from dataclasses import dataclass
from fractions import Fraction
import functools
import hashlib
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
    ProofExportError, _rounded, bound_combination_refutes, integer_tightened, is_uninterpreted_sort,
    linear_combination_refutes, numeral_value, parse_assertions, query_snapshot,
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
_REAL_NAMES = {z3.Z3_OP_ADD: "+", z3.Z3_OP_SUB: "-", z3.Z3_OP_UMINUS: "-", z3.Z3_OP_MUL: "*", z3.Z3_OP_DIV: "/"}
_REAL_ARITY = {z3.Z3_OP_UNINTERPRETED: 0, z3.Z3_OP_ANUM: 0, z3.Z3_OP_UMINUS: 1, z3.Z3_OP_DIV: 2}
# The integer operators, Int certificates only: div and mod by a nonzero
# numeral are Lean's Euclidean Int division and remainder (/ and %, which
# agree with SMT-LIB's away from zero; a zero divisor is rejected, see
# _integer_divisor), abs is the ite SMT-LIB defines it as. rem, a Z3
# extension, is Z3's definition (ite (>= k 0) (mod t k) (- (mod t k)))
# evaluated at its numeral divisor k: t % k for a positive k, -(t % k) for a
# negative one. All four are
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
_HINTS = _COEFFICIENT_HINTS + ("euf", "tseitin", "smt", "cnf", "triangle-eq", "arith")
_FRAGMENTS = ("propositional", "qf_lra", "qf_lia", "qf_uf", "qf_uflra", "qf_uflia")
# The arithmetic sorts and their Lean carriers: Real variables are valued in
# Rat (see the exporter README for the soundness argument), Int variables in
# Int, where omega decides the linear integer lemmas (see _grind_lemma).
_ARITH_SORTS = ("Real", "Int")
_NUMBER_TYPES = {"Real": "Rat", "Int": "Int"}
# The fragments mixing arithmetic with uninterpreted symbols, by arithmetic sort.
_MIXED_FRAGMENTS = {"Real": "qf_uflra", "Int": "qf_uflia"}
# Refutations with more proof steps than this are split into separately
# checked lemmas, none nesting more than _OUTLINE_CHUNK_STEPS steps: one
# nested term elaborates superlinearly and exhausts the default heartbeat
# budget between 1,000 and 2,000 steps.
_OUTLINE_PROOF_STEPS = 500
_OUTLINE_CHUNK_STEPS = 500
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
# valuation stays a parameter of its own, as in QF_LRA and QF_LIA.
_NUMERIC_FIELDS = {"Real": (("real", "Rat -> U"), ("rfuns", "Nat -> List U -> Rat")),
                   "Int": (("int", "Int -> U"), ("ifuns", "Nat -> List U -> Int"))}
_UFLRA_BINDERS = " (_vars : Nat -> Rat)" + _UF_BINDERS
_UFLRA_ARGUMENTS = " _vars" + _UF_ARGUMENTS
_UFLIA_BINDERS = " (_vars : Nat -> Int)" + _UF_BINDERS
_UFLIA_ARGUMENTS = " _vars" + _UF_ARGUMENTS
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
    numeric: str = "Real"  # the one arithmetic sort of the certificate, Real or Int

    @property
    def fragment(self):
        if self.arithmetic and self.uninterpreted:
            return _MIXED_FRAGMENTS[self.numeric]
        if self.arithmetic:
            return "qf_lia" if self.numeric == "Int" else "qf_lra"
        return "qf_uf" if self.uninterpreted else "propositional"

    @property
    def valuation(self):
        """Extra Lean arguments of every formula: the numeric valuation, the uninterpreted interpretation, or both."""
        return {"qf_lra": " _vars", "qf_lia": " _vars", "qf_uf": _UF_ARGUMENTS,
                "qf_uflra": _UFLRA_ARGUMENTS, "qf_uflia": _UFLIA_ARGUMENTS}.get(self.fragment, "")

    @property
    def number_type(self):
        """The Lean type valuing the arithmetic variables: Rat for Real, Int for Int."""
        return _NUMBER_TYPES[self.numeric]

    @property
    def injection(self):
        """The map injecting a numeric argument of a function or predicate into the carrier."""
        return _INJECTIONS[self.numeric]

    @property
    def numeric_functions(self):
        """The indexed family of functions with a numeric result."""
        return _NUMERIC_FUNCTIONS[self.numeric]

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

    def conclusion(self, node):
        return self.arguments(node)[-1]

    def clause(self, node):
        if self.kind(node) == z3.Z3_OP_FALSE:
            return ()
        if self.kind(node) == z3.Z3_OP_OR:
            return self.arguments(node)
        return (node,)


def _parameters(kind, name, parameters):
    """Validate declaration parameters: only th-lemma carries a hint and its coefficients."""
    parameters = _list(parameters, "declaration parameters")
    if any(type(parameter) is not str for parameter in parameters):
        raise ReconstructionError("declaration parameters must be strings")
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
    """Return the uninterpreted sort names used by the declarations, sorted."""
    sorts = set()
    for raw in raws:
        if type(raw) is dict:
            sorts.update(sort for sort in [raw.get("range")] + _list(raw.get("domain", []), "declaration domain")
                         if type(sort) is str and sort not in _RESERVED_SORTS)
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
    # Real, or Int (the last three injected into the carrier; a certificate
    # never mixes Real with Int, see _validate_graph); Proof is never an argument.
    argument_sorts = sorts + ("Bool", "Real", "Int")
    if raw["range"] in sorts:
        # Constants, functions, and ite inhabit an uninterpreted sort: no definitions.
        if kind == z3.Z3_OP_ITE:
            if name != "if" or domain != ("Bool", raw["range"], raw["range"]):
                raise ReconstructionError("invalid uninterpreted-sort ite declaration")
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
        if kind in _ARITH_PREDICATE_NAMES:
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
    if len(numeric_sorts) > 1:
        raise ReconstructionError("certificates cannot mix Int and Real arithmetic")
    arithmetic = bool(numeric_sorts)
    numeric = numeric_sorts.pop() if numeric_sorts else "Real"
    if arithmetic and certificate["fragment"] in ("propositional", "qf_uf"):
        raise ReconstructionError("%s certificates cannot contain arithmetic" % certificate["fragment"])
    uninterpreted = bool(sorts) or any(decl.kind == z3.Z3_OP_UNINTERPRETED and decl.domain for decl in declarations)
    if uninterpreted != (certificate["fragment"] in ("qf_uf", "qf_uflra", "qf_uflia")):
        raise ReconstructionError("only qf_uf, qf_uflra, and qf_uflia certificates declare an uninterpreted sort "
                                  "or function, and they must use one")
    graph = _Graph(declarations, tuple(nodes), assertions, root, arithmetic, sorts, uninterpreted, numeric)
    if graph.fragment != certificate["fragment"]:
        if not arithmetic:
            raise ReconstructionError("%s certificates must contain arithmetic" % certificate["fragment"])
        # The uninterpreted symbols agree with the label (checked above), so
        # the label names the other arithmetic sort.
        raise ReconstructionError("only qf_lia and qf_uflia certificates contain Int arithmetic, "
                                  "and they contain no other")
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
# into them, predicates, and functions with a Real or Int result. Each table
# maps a name to its declaration.
_SYMBOL_TABLES = {
    ("Bool", False): "atoms", ("Real", False): "variables", ("Int", False): "variables",
    ("sort", False): "elements", ("sort", True): "functions", ("Bool", True): "predicates",
    ("Real", True): "numeric_functions", ("Int", True): "numeric_functions",
}
_TABLE_LABELS = {
    "atoms": "Atom", "variables": "Variable", "elements": "Element", "functions": "Function",
    "predicates": "Predicate", "numeric_functions": "%s function",  # filled with the arithmetic sort
}


def _symbol_table(range_name, arity, sorts):
    return _SYMBOL_TABLES.get(("sort" if range_name in sorts else range_name, arity > 0))


def _sort_name(sort):
    """The certificate's name for a sort of the original input."""
    kind = sort.kind()
    if kind == z3.Z3_BOOL_SORT:
        return "Bool"
    if kind == z3.Z3_REAL_SORT:
        return "Real"
    if kind == z3.Z3_INT_SORT:
        return "Int"
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
    sorts never compare equal even though Lean renders every sort as _m.U.
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

    for index, node in enumerate(graph.nodes):
        decl = graph.decl(index)
        if decl.range == "Proof":
            continue
        name = ""
        if decl.kind == z3.Z3_OP_UNINTERPRETED:
            name = decl.name
            table = _symbol_table(decl.range, len(decl.domain), graph.sorts)
            if table is None:
                raise ReconstructionError("unsupported symbol signature: %s" % name)
            if name in tables[table] and tables[table][name] != node.declaration:
                raise ReconstructionError("ambiguous %s symbol identity: %s" % (
                    {"atoms": "Boolean", "variables": graph.numeric,
                     "numeric_functions": graph.numeric + " function"}.get(table, table[:-1]), name))
            if any(name in other for key, other in tables.items() if key != table):
                raise ReconstructionError("symbol used with two sorts: %s" % name)
            tables[table][name] = node.declaration
        elif decl.kind == z3.Z3_OP_ANUM:
            name = str(Fraction(decl.name))
        terms[index] = intern(decl.kind, name, decl.range, (terms[arg] for arg in node.arguments))

    original_terms, original_sorts = {}, set()
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
        if is_uninterpreted_sort(expr.sort()):
            original_sorts.add(range_name)
        if decl.kind() == z3.Z3_OP_UNINTERPRETED:
            name = str(decl.name())
            table = _symbol_table(range_name, decl.arity(), graph.sorts)
            if table is None:
                raise ReconstructionError("certificate sort does not match the original input")
            signature = (tuple(_sort_name(decl.domain(i)) for i in range(decl.arity())), range_name)
            if original_symbols[table].setdefault(name, signature) != signature:
                raise ReconstructionError("symbol declared with several signatures: %s" % name)
        elif decl.kind() == z3.Z3_OP_ANUM:
            name = str(numeral_value(expr))
        original_terms[expr.get_id()] = intern(
            decl.kind(), name, range_name, (original_terms[child.get_id()] for child in expr.children()))
    if original_sorts != set(graph.sorts):
        raise ReconstructionError("certificate sort does not match the original input")
    if any(set(tables[table]) != set(original_symbols[table]) for table in tables):
        raise ReconstructionError("certificate assertions do not match the original input")
    for table, symbols in tables.items():
        for name, declaration in symbols.items():
            decl = graph.declarations[declaration]
            if (decl.domain, decl.range) != original_symbols[table][name]:
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
    return {"qf_lra": " (_vars : Nat -> Rat)", "qf_lia": " (_vars : Nat -> Int)", "qf_uf": _UF_BINDERS,
            "qf_uflra": _UFLRA_BINDERS, "qf_uflia": _UFLIA_BINDERS}.get(graph.fragment, "")


def _interpretation_structure(graph):
    """Declare the structure whose one argument _m interprets the uninterpreted symbols (none outside the UF fragments)."""
    if not graph.uninterpreted:
        return []
    fields = _UF_FIELDS + (_NUMERIC_FIELDS[graph.numeric] if graph.arithmetic else ())
    return ["structure Interpretation where"] + ["  %s : %s" % field for field in fields] + [""]


def _infix(operator, arguments):
    result = arguments[0]
    for argument in arguments[1:]:
        result = "(%s %s %s)" % (result, operator, argument)
    return result


def _application_arguments(graph, arguments, term, formula):
    """Render the argument list of a function or predicate over the uninterpreted sorts.

    A Boolean argument is injected into the carrier by _m.bool (its formula is
    rendered as a Prop) and a Real or Int one by _m.real or _m.int.
    """
    return "[%s]" % ", ".join("(%s %s)" % (graph.injection, term(arg)) if graph.is_arith(arg)
                              else term(arg) if graph.is_term(arg)
                              else "(_m.bool %s)" % formula(arg) for arg in arguments)


def _numeral(graph, value):
    """Render a rational as a literal of the certificate's number type; Int numerals are integers."""
    if value.denominator == 1:
        return "((%d : %s))" % (value.numerator, graph.number_type)
    if graph.numeric == "Int":
        raise ReconstructionError("fractional value in an Int certificate: %s" % value)
    return "((%d : Rat) / (%d : Rat))" % (value.numerator, value.denominator)


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
        if not arguments:
            return ("_vars %d" if graph.is_arith(node) else "_m.elems %d") % index
        return "%s %d %s" % (graph.numeric_functions if graph.is_arith(node) else "_m.funs", index,
                             _application_arguments(graph, arguments, term, formula))
    if kind == z3.Z3_OP_ANUM:
        return _numeral(graph, Fraction(graph.decl(node).name))
    if kind == z3.Z3_OP_ITE:
        # The instance's proposition is inferred from the condition.
        return "(@ite %s %s (Classical.propDecidable _) %s %s)" % (
            graph.number_type if graph.is_arith(node) else "_m.U",
            formula(arguments[0]), term(arguments[1]), term(arguments[2]))
    args = [term(arg) for arg in arguments]
    if kind == z3.Z3_OP_UMINUS:
        return "(-%s)" % args[0]
    if kind == z3.Z3_OP_ABS:
        # SMT-LIB's definition; the instance's proposition is inferred from the condition.
        return "(@ite %s (%s >= ((0 : %s))) (Classical.propDecidable _) %s (-%s))" % (
            graph.number_type, args[0], graph.number_type, args[0], args[0])
    if kind in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD):
        return "(%s %s %s)" % (args[0], "/" if kind == z3.Z3_OP_IDIV else "%", args[1])
    if kind == z3.Z3_OP_REM:
        # Z3's (ite (>= k 0) (mod t k) (- (mod t k))) at the numeral divisor k.
        remainder = "(%s %% %s)" % (args[0], args[1])
        return remainder if _integer_divisor(graph, node) > 0 else "(-%s)" % remainder
    return _infix(_REAL_NAMES[kind], args)


def _formula_body(graph, node, atom_indices, term=None, formula=None):
    """Render a Bool node; term and formula render its children (defaults: by definition name).

    atom_indices numbers the Boolean atoms and the predicates, each from zero.
    """
    term = (lambda child: _term(graph, child)) if term is None else term
    formula = (lambda child: _formula(graph, child)) if formula is None else formula
    kind = graph.kind(node)
    arguments = graph.arguments(node)
    if kind == z3.Z3_OP_UNINTERPRETED and arguments:
        return "_m.preds %d %s" % (atom_indices[graph.nodes[node].declaration],
                                   _application_arguments(graph, arguments, term, formula))
    if arguments and graph.is_term(arguments[0]):
        args = [term(arg) for arg in arguments]
        if kind in _ARITH_PREDICATE_NAMES and graph.is_arith(arguments[0]):
            return "(%s %s %s)" % (args[0], _ARITH_PREDICATE_NAMES[kind], args[1])
        if kind == z3.Z3_OP_EQ:
            return "(%s = %s)" % tuple(args)
        if kind == z3.Z3_OP_DISTINCT:
            pairs = ["(Not (%s = %s))" % (left, right)
                     for index, left in enumerate(args) for right in args[index + 1:]]
            return _fold("And", pairs, "True")
        raise ReconstructionError("unsupported arithmetic atom")
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
                    else "(congrArg %s %s)" % (graph.injection, argument) if graph.is_arith(first) else argument
                    for first, argument in zip(left_args, arguments)]
        if graph.is_term(left):
            return "(congrArg (%s %d) %s)" % (graph.numeric_functions if graph.is_arith(left) else "_m.funs",
                                              variable_indices[graph.nodes[left].declaration],
                                              _list_congruence(elements)), False, []
        return "(Iff.of_eq (congrArg (_m.preds %d) %s))" % (atom_indices[graph.nodes[left].declaration],
                                                             _list_congruence(elements)), False, []
    if graph.is_term(left):
        if kind == z3.Z3_OP_ITE:
            return "(ite_congr_classical %s %s %s)" % tuple(arguments), True, []
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


def _reachable(graph, conclusion):
    """Return the formula and term nodes reachable from a conclusion, and whether any is a theory node.

    Theory nodes are Real and uninterpreted-sort terms and predicate
    applications (which may take Boolean arguments only); a conclusion without
    them is purely propositional over the atoms.
    """
    reachable, pending, theory = set(), [conclusion], False
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


def _trivial_distinct(graph, node):
    """A distinct of one argument, which the input may state and Z3 rewrites to true."""
    return graph.kind(node) == z3.Z3_OP_DISTINCT and len(graph.arguments(node)) == 1


def _inline(graph, node, atom_indices, variable_indices):
    """Render a formula or term with every definition expanded, as unfold would."""
    def child(sub):
        return "(%s)" % _inline(graph, sub, atom_indices, variable_indices)
    if graph.is_term(node):
        return _term_body(graph, node, variable_indices, child, child)
    return _formula_body(graph, node, atom_indices, child, child)


def _scaling_helpers(graph, reachable, atom_indices, variable_indices):
    """State denominator-free forms of fractional atoms, which grind proves and then uses.

    grind's linear arithmetic over Rat does not always combine equalities whose
    constants are fractions, while it handles the same facts once scaled to
    integers. Each helper is an implication from the atom to its scaled form.
    """
    helpers = []
    for formula in sorted(reachable):
        kind, arguments = graph.kind(formula), graph.arguments(formula)
        if (graph.is_arith(formula) or not arguments or not graph.is_arith(arguments[0])
                or (kind not in _ARITH_PREDICATE_NAMES and kind != z3.Z3_OP_EQ)):
            continue
        relation, terms, constant = _atom_constraint(graph, formula)
        scale = _common_denominator(terms, constant)
        if scale == 1:
            continue
        helpers.append("  have _s%d : %s -> (%s %s ((0 : %s))) := by grind" % (
            formula, _inline(graph, formula, atom_indices, variable_indices),
            _scaled_form(graph, terms, constant, scale, atom_indices, variable_indices), relation,
            graph.number_type))
    return helpers


def _common_denominator(terms, constant):
    scale = 1
    for value in list(terms.values()) + [constant]:
        scale = scale * value.denominator // _gcd(scale, value.denominator)
    return scale


def _scaled_form(graph, terms, constant, scale, atom_indices, variable_indices):
    """Render scale * (terms + constant) with integer coefficients, as grind's linear module wants it."""
    # The linear form's variables are Real variables and opaque ite terms.
    parts = ["((%d : %s)) * %s" % (terms[variable] * scale, graph.number_type,
                                   _inline(graph, variable, atom_indices, variable_indices))
             for variable in sorted(terms)]
    parts.append("((%d : %s))" % (constant * scale, graph.number_type))
    return " + ".join(parts)


def _ite_gate_helpers(graph, reachable, atom_indices, variable_indices):
    """State the branch equalities of every reachable Real ite, denominator-free.

    grind splits on an ite term by itself, but when the selected branch is a
    fractional numeral or a term with fractional coefficients it does not
    combine the resulting equality with its linear facts, just as with
    fractional atoms. Each helper gives one branch equality under the condition
    or its negation, scaled to integer coefficients, so grind can use it.
    """
    helpers = []
    for node in sorted(reachable):
        if not graph.is_arith(node) or graph.kind(node) != z3.Z3_OP_ITE:
            continue
        condition, then_branch, else_branch = graph.arguments(node)

        def inline(sub):
            return "(%s)" % _inline(graph, sub, atom_indices, variable_indices)

        for side, branch, hypothesis, lemma in (
                (0, then_branch, inline(condition), "ite_eq_left"),
                (1, else_branch, "(Not %s)" % inline(condition), "ite_eq_right")):
            terms = {}
            try:
                constant = _linear_term(graph, branch, Fraction(1), terms)
            except ReconstructionError:
                # A branch without a linear form, such as the dead branch
                # dividing by zero in the rewriter's factor cancellation
                # (see _validate_graph): no helper, grind splits unaided.
                continue
            scale = _common_denominator(terms, constant)
            if scale == 1:
                helpers.append("  have _g%d_%d : %s -> %s = %s := fun _h => %s _h" % (
                    node, side, hypothesis, inline(node), inline(branch), lemma))
            else:
                helpers.append("  have _g%d_%d : %s -> ((%d : %s)) * %s = (%s) := fun _h => by rw [%s _h]; grind" % (
                    node, side, hypothesis, scale, graph.number_type, inline(node),
                    _scaled_form(graph, terms, constant, scale, atom_indices, variable_indices), lemma))
    return helpers


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
    atoms = _opaque_int_atoms(graph, conclusions) if opaque_tactic else []
    budget = _LATTICE_LEMMA_HEARTBEATS if atoms and _lattice_step(graph, node) else 1000000
    lines = [
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
        alternatives.append(
            facts
            + ["generalize %s = _o%d" % (_term(graph, atom), position) for position, atom in enumerate(atoms)]
            + [opaque_tactic])
        remaining = inside
    else:
        remaining = reachable
    fallback = ["unfold " + " ".join(_definition_names(graph, remaining))] if remaining else []
    fallback.extend(helper.strip() for helper in _theory_helpers(graph, reachable, atom_indices, variable_indices))
    fallback.append(_theory_tactic(graph))
    alternatives.append(fallback)
    if len(alternatives) == 1:
        lines.extend("  " + tactic for tactic in fallback)
    else:
        lines.append("  first")
        lines.extend("    | (" + "\n       ".join(alternative) + ")" for alternative in alternatives)
    return lines, "(%s_%d _atoms%s%s)" % (prefix, node, graph.valuation,
                                          "".join(" _step_%d" % premise for premise in premises))


def _definition_names(graph, nodes):
    """The definitions of nodes in unfolding order: parents before children (ids are topological)."""
    return ["%s_%d" % ("term" if graph.is_term(formula) else "formula", formula)
            for formula in sorted(nodes, reverse=True)]


def _theory_helpers(graph, reachable, atom_indices, variable_indices):
    helpers = []
    if graph.arithmetic:
        helpers.extend(_scaling_helpers(graph, reachable, atom_indices, variable_indices))
        helpers.extend(_ite_gate_helpers(graph, reachable, atom_indices, variable_indices))
    if graph.uninterpreted:
        helpers.extend(_boolean_argument_helpers(graph, reachable, atom_indices, variable_indices))
    if graph.arithmetic and graph.uninterpreted:
        helpers.extend(_real_argument_helpers(graph, reachable, atom_indices, variable_indices))
    return helpers


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
    omega reads % by a positive numeral only, so the facts are the library's
    (Int.emod_neg folds a negative divisor into its opposite). The facts are
    best effort: Int.emod_neg expects the divisor rendered as the negation
    of a numeral, which is how Z3 writes a negative constant; should a fact
    fail to prove, the generalized attempt fails and the fallback runs.
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
            upper = "rw [Int.emod_neg]; " + upper
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
        groups.setdefault(_real_atom_key(graph, atom), []).append(atom)
    lines, names = [], []
    for members in groups.values():
        for first, second in zip(members, members[1:]):
            definitions = _definition_names(graph, _reachable(graph, first)[0] | _reachable(graph, second)[0])
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
    if graph.numeric != "Int" or parameters[0] not in ("farkas", "bound", "cut"):
        return None
    return "omega" if len(parameters) > 1 else "grind (splits := 64)"


def _lattice_step(graph, node):
    """Whether node is an Int th-lemma without coefficients: a cut, or a farkas or bound Z3 did not explain."""
    decl = graph.decl(node)
    return (graph.numeric == "Int" and decl.name == "th-lemma" and len(decl.parameters) == 1
            and decl.parameters[0] in ("farkas", "bound", "cut"))


def _farkas_combination(graph, node):
    """Tactic lines proving an Int farkas or bound th-lemma by the combination its coefficients give, or None.

    The reconstructor re-derived the combination (_check_th_lemma), so the
    proof need not search for one: every premise, and the negation of every
    clause literal, is a bound `lower <= upper` over Int (a strict bound
    tightened by one, an equality oriented by the sign of its multiplier),
    stated as the fact 0 <= upper - lower by a core lemma; the facts scaled
    by their integer multipliers sum to a negative constant, an identity
    omega checks before any hypothesis is in scope, where it only has to
    normalize the sum. With the bounds in scope omega searches for the
    combination itself: two 21-literal Farkas lemmas over twenty variables
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
    if graph.numeric != "Int" or not _combination_certified(graph, node):
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
    # The identity goes first, while omega sees no hypothesis but the
    # valuation, over the atoms of the linear forms left folded (delta
    # unfolds the sums, products, and numerals above them in one pass, and
    # omega reads a folded atom as one variable). The rest is one
    # term, typed by the ascription of the sum: a tactic `have` per fact
    # cost Lean about two megabytes per lemma, which a certificate of 800
    # two-literal Farkas lemmas (the wide division seed) could not afford.
    return [
        _sum_identity(graph, "_sum", combination, total, sides),
        "exact %sClassical.byContradiction fun _hn => %s" % (
            "".join("fun _p%d => " % position for position in range(premises)),
            _combination_absurd(nonnegative, combination, "_sum")),
    ]


def _sum_identity(graph, name, combination, total, sides):
    """The tactic line stating that a combination of facts sums to its constant, proved by omega."""
    return "have %s : %s = ((%d : Int)) := by %somega" % (
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
    combination, nonnegative = summands[-1], proofs[-1]
    for summand, proof in zip(reversed(summands[:-1]), reversed(proofs[:-1])):
        combination = "(%s + %s)" % (summand, combination)
        nonnegative = "(Int.add_nonneg %s %s)" % (proof, nonnegative)
    return combination, nonnegative, int(total * scale), sides


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


_LINEAR_ATOM_KINDS = (z3.Z3_OP_UNINTERPRETED, z3.Z3_OP_ITE, z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM, z3.Z3_OP_ABS)


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
    return "omega" if graph.numeric == "Int" else "grind (splits := 64)"


_OPAQUE_INT_KINDS = (z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM, z3.Z3_OP_ABS, z3.Z3_OP_ITE, z3.Z3_OP_UNINTERPRETED)


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
    """The outermost opaque Int atoms under the formulas, outer atoms first (ids are topological)."""
    atoms, pending, seen = set(), list(formulas), set()
    while pending:
        node = pending.pop()
        if node in seen:
            continue
        seen.add(node)
        if _is_opaque_int_atom(graph, node):
            atoms.add(node)
        elif not _trivial_distinct(graph, node):
            pending.extend(graph.arguments(node))
    return sorted(atoms, reverse=True)


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
    """
    return "first | omega | grind (splits := 64)" if graph.numeric == "Int" else "grind (splits := 64)"


def _boolean_argument_helpers(graph, reachable, atom_indices, variable_indices):
    """State excluded middle for every formula that is a Boolean argument of an application.

    Z3's egraph merges each Boolean argument with true or false as soon as
    the SAT solver assigns it, so its lemmas may rest on the two cases of an
    argument that no premise mentions, for example when preprocessing
    combined several assertions. grind splits on disjunctions in context but
    not on arbitrary propositions, so each case split is offered explicitly;
    from either case it derives _m.bool p = _m.bool True or _m.bool p = _m.bool False
    by congruence.
    """
    arguments = set()
    for node in sorted(reachable):
        if graph.kind(node) == z3.Z3_OP_UNINTERPRETED:
            arguments.update(argument for argument in graph.arguments(node)
                             if not graph.is_term(argument)
                             and graph.kind(argument) not in (z3.Z3_OP_TRUE, z3.Z3_OP_FALSE))
    helpers = []
    for argument in sorted(arguments):
        formula = _inline(graph, argument, atom_indices, variable_indices)
        helpers.append("  have _b%d : Or (%s) (Not (%s)) := Classical.em _" % (argument, formula, formula))
    return helpers


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
    """
    groups = {}
    for node in sorted(reachable):
        if graph.kind(node) != z3.Z3_OP_UNINTERPRETED:
            continue
        for argument in graph.arguments(node):
            if graph.is_arith(argument):
                members = groups.setdefault(_real_argument_key(graph, argument), [])
                if argument not in members:
                    members.append(argument)
    helpers = []
    for members in groups.values():
        for first, second in zip(members, members[1:]):
            helpers.append("  have _r%d_%d : %s = %s := by %s" % (
                first, second, _inline(graph, first, atom_indices, variable_indices),
                _inline(graph, second, atom_indices, variable_indices), _theory_tactic(graph)))
    return helpers


def _real_argument_key(graph, node):
    """The linear form of a Real or Int term, with its ite atoms keyed up to Z3's normalization.

    Variables and applications are atoms of their own; an ite whose condition
    is a linear atom is keyed by the canonical form of that condition
    (_condition_key: swapping the branches when the condition is the
    complement of the canonical atom) and by the keys of its branches. Two
    terms with one key denote the same value, which the theory tactic
    proves and the helper states.
    """
    terms = {}
    constant = _linear_term(graph, node, Fraction(1), terms)
    atoms = [(_real_atom_key(graph, atom), value) for atom, value in terms.items() if value != 0]
    return (tuple(sorted(atoms, key=repr)), constant)


def _real_atom_key(graph, atom):
    """The key of an atom of the linear forms: an ite up to Z3's normalization, abs as its ite, else itself.

    An ite is keyed by the canonical form of its condition (_condition_key)
    and the keys of its branches, swapped when the canonical condition is
    the complement. An ite whose condition is no linear atom, or with a
    branch outside the linear forms (the dead branch dividing by zero in
    the rewriter's factor cancellation, see _validate_graph), is opaque:
    its own key.
    """
    try:
        return _ite_atom_key(graph, atom)
    except ReconstructionError:
        return ("atom", atom)


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
        elif graph.numeric == "Int":
            keyed, constant = _rounded(keyed, constant)
            if leading < 0:
                keyed = {key: -value for key, value in keyed.items()}
                constant, swapped = 1 - constant, not swapped
        else:
            keyed = {key: value / abs(leading) for key, value in keyed.items()}
            constant /= abs(leading)
    return (relation, tuple(sorted(keyed.items(), key=repr)), constant), swapped


def _boolean_structure(graph, node, atom_indices, memo=None, leaves=None):
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
    atom is unsupported. A distinct over terms whose every pair has an
    equality node of its own (the alldiff literals Z3 logs) is instead the
    conjunction of those equalities negated, the leaves in the order
    _formula_body renders the pairs, so the literal (not (= a b)) of a
    clause names a conjunct of the distinct: a cnf lemma tying such a
    literal to an assertion holding the distinct (QF_UF NEQ004) was out of
    the prover's reach and unfolded the whole assertion into grind.

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
            pairs = _distinct_pair_equalities(graph, current)
            if pairs is None:
                memo[current] = leaves.setdefault(current, ("leaf", current, _formula(graph, current)))
            else:
                memo[current] = _structure_fold("and", [
                    ("not", leaves.setdefault(pair, ("leaf", pair, _formula(graph, pair)))) for pair in pairs])
        else:
            pending.append((current, True))
            pending.extend((argument, False) for argument in reversed(arguments))
    return memo[node]


def _distinct_pair_equalities(graph, node):
    """The equality nodes of a distinct's argument pairs, in rendering order, or None.

    None unless node is a distinct over terms and every pair (a, b), a
    before b, has the node (= a b): a pair logged as (= b a) renders as
    another proposition than the conjunct (Not (a = b)) of the distinct.
    """
    if graph.kind(node) != z3.Z3_OP_DISTINCT:
        return None
    arguments = graph.arguments(node)
    pairs = [graph.equalities.get((left, right))
             for index, left in enumerate(arguments) for right in arguments[index + 1:]]
    return None if None in pairs else pairs


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


def _reject_disjunction(proofs):
    """A refutation of a right-nested disjunction from refutations of all its disjuncts (not_or.mpr)."""
    result = proofs[-1]
    for proof in reversed(proofs[:-1]):
        result = "(not_or.mpr (And.intro %s %s))" % (proof, result)
    return result


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
    """

    def __init__(self, *roots, classical=False, names=None, links=False):
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
        self.constants = [(structure, structure[0] == "true", "True.intro" if structure[0] == "true"
                           else "(fun _absurd => _absurd)")
                          for structure in (("true",), ("false",)) if structure in self.parents]

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

    def _exhausted(self):
        return self.steps > _STRUCTURAL_REWRITE_STEPS or self.chars > _STRUCTURAL_REWRITE_CHARS

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
        """
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
        return lines, facts

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
        if self.linked:
            negation = self.name()
            lines = self._prove(dict(), ("false",), self.constants + list(facts)
                                + [(source, True, hypothesis), (target, False, negation)])
            if lines is None:
                return None
            return hypothesis, ["refine Classical.byContradiction (fun (%s : Not %s) => ?_)" % (
                negation, self._render(target))] + lines
        lines = self._prove(dict(), target, self.constants + list(facts) + [(source, True, hypothesis)])
        if lines is None:
            return None
        return hypothesis, lines

    def refutation(self, structure, facts=()):
        """Tactic lines proving the goal Not structure under the named facts (hypotheses in scope), or None."""
        hypothesis = self.name()
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
        """
        splits = []  # open splits: (lines, branch facts, state, header, names, branches)
        result = self._settle(state, target, facts)
        while True:
            if isinstance(result, tuple):  # a split: prove its first branch
                splits.append(result)
            elif result is None:
                return None  # a branch not proved fails the whole proof
            elif not splits:
                return result
            else:
                splits[-1][5].append(result)
            lines, branch_facts, state, header, names, branches = splits[-1]
            if len(branches) == len(branch_facts):
                splits.pop()
                result = lines + [header(names)] + _bullets(branches)
                continue
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
        atoms = sorted((-len(self.parents[atom]), atom[1], atom) for atom in self.parents
                       if atom[0] in self.decidable and atom not in state)
        if not atoms:
            return None  # every atom assigned without the target holding: the equivalence does not hold
        atom = atoms[0][2]
        if self.classical:
            split = "(Classical.em %s)" % _render_structure(atom)
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
        for position, structure in enumerate(self.order):
            value = state.get(structure)
            if structure[0] != "or" or value is None or not value[0]:
                continue
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
        pending.extend(self.parents[structure])
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
            if value is not None and value[0]:
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
    steps in one term: both exhausted the heartbeats). The unfolded theory
    proof (_grind_lemma) stays the fallback, taken by `first` when the
    structural attempt is not found or does not check, and alone when the
    prover gives up (the clause needs a theory fact: the alldiff clauses Z3
    simplified under a unit rest on the value of an ite under the distinct).
    """
    conclusion = graph.conclusion(node)
    leaves, memo = {}, {}
    structure = _boolean_structure(graph, conclusion, atom_indices, memo, leaves)
    bridges = _leaf_bridges(graph, leaves)
    prover = _PropositionalProver(("not", structure), *[bridge for bridge, _ in bridges], classical=True,
                                  names=_structure_names(graph, memo))
    names = [prover.name() for _ in bridges]
    refutation = prover.refutation(("not", structure), [(bridge, name) for (bridge, _), name in zip(bridges, names)])
    if refutation is None:
        return _grind_lemma(graph, node, "th_lemma", atom_indices, variable_indices,
                            opaque_tactic=_opaque_tactic(graph, node))
    # The goal is the clause's definition, which the refutation's hypothesis
    # unifies with (its structure is named by that definition); nothing is
    # unfolded before the attempt, and the fallback unfolds everything.
    attempt = ["have %s : %s := by unfold %s; %s" % (name, _render_structure(bridge), " ".join(definitions),
                                                     _theory_tactic(graph))
               for (bridge, definitions), name in zip(bridges, names)]
    attempt.append("refine Classical.byContradiction ?_")
    attempt.extend(refutation)
    return _grind_lemma(graph, node, "th_lemma", atom_indices, variable_indices,
                        opaque_tactic=_opaque_tactic(graph, node), structural=attempt)


def _leaf_bridges(graph, leaves):
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
        definitions = _definition_names(graph, _reachable(graph, leaf)[0] | _reachable(graph, other)[0])
        right = ("not", leaves[other]) if negated else leaves[other]
        result.append((("iff", leaves[leaf], right), definitions))
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
        if graph.numeric == "Int" and relation == "<=":
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
    if theory and terms is not None and terms[left] == terms[right]:
        return [], set(), "(%s.refl %s)" % (_relation(graph, left), _side(graph, left))
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
            lines, term = _grind_lemma(graph, node, "rewrite", atom_indices, variable_indices,
                                       opaque_tactic=_opaque_rewrite_tactic(graph))
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


def _normalized_atom(graph, atom, order):
    """The canonical key of an arithmetic atom's linear form, and whether the atom is its negation.

    The key is (relation, ((order(term), coefficient), ...), constant) with
    the terms sorted by order and the first one's coefficient scaled to 1
    (its absolute value for <=), so that positive multiples of one
    constraint share a key. Over Int every atom is already tightened to
    t <= 0, whose complement is -t + 1 <= 0: a form with a negative leading
    coefficient is keyed as the negation of its complement, so that (< x 5)
    and (>= x 5) share one atom (the replay's _Normalizer does the same)
    and the propositional lemma sees them as complementary.
    """
    relation, terms, constant = _atom_constraint(graph, atom)
    negated = relation == "<"
    if negated:
        terms, constant, relation = {var: -value for var, value in terms.items()}, -constant, "<="
    first = min(terms, key=order) if terms else None
    if graph.numeric == "Int" and relation == "<=" and terms and terms[first] < 0:
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
        representatives[ite] = tables.setdefault(table, ite)
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
    def numeral(value):
        return _numeral(graph, value)

    representatives = _ite_representatives(graph, atoms)

    def order(variable):
        # Variables by index, then opaque terms by node, an ite by its
        # representative's (see _normalizable_rewrite).
        if not graph.arguments(variable):
            return 0, variable_indices[graph.nodes[variable].declaration]
        return 1, representatives.get(variable, variable)

    def render(key):
        kind, index = key
        if kind == 0:
            return "_vars %d" % index
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
        parts = ["(%s * %s)" % (numeral(value * scale), render(var)) for var, value in ordered]
        parts.append(numeral(constant * scale))
        expression = "(%s %s ((0 : %s)))" % (" + ".join(parts), relation, graph.number_type)
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
    any double negation, so the lemma stays axiom-free.
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

    Variables, ite terms, integer div, mod, and rem, and abs are the atoms
    of the linear form; each is opaque to Farkas reasoning, an ite tied to
    its branches by gate clauses and a div, mod, or rem to its operands by
    the solver's arith axioms.
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
        variable = None
        for arg in arguments:
            factor_terms = {}
            factor = _linear_term(graph, arg, Fraction(1), factor_terms)
            if factor_terms:
                if variable is not None:
                    raise ReconstructionError("nonlinear multiplication in a theory lemma")
                variable = arg
            else:
                scale *= factor
        if variable is None:
            return scale
        return _linear_term(graph, variable, scale, terms)
    if kind == z3.Z3_OP_DIV:
        divisor = _linear_term(graph, arguments[1], Fraction(1), {})
        if divisor == 0:
            raise ReconstructionError("division by zero in a theory lemma")
        return _linear_term(graph, arguments[0], scale / divisor, terms)
    raise ReconstructionError("unsupported arithmetic term in a theory lemma")


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
    if graph.numeric == "Int":
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
            _atom_constraint(graph, atom)
        return
    if parameters[0] not in _COEFFICIENT_HINTS:
        return
    coefficients = [Fraction(parameter) for parameter in parameters[1:]]
    if parameters[0] == "cut" or (parameters[0] in ("farkas", "bound") and graph.numeric == "Int"
                                  and not coefficients):
        # An integer cut or gcd conflict, or an integer Farkas or bound step
        # whose LP explanation rested on cuts or on the integer lattice
        # (the legacy core labels a lattice conflict farkas with coefficients
        # that do not re-derive, or unsupported when its own check fails):
        # the exporter kept no coefficients because none certify the
        # rounding, so only the shape is checked (integer linear atoms, held
        # premises included) and Lean proves the clause or the implication.
        # (A coefficient-free farkas or bound over Real falls through to the
        # coefficient count check below.)
        if parameters[0] == "cut" and (graph.numeric != "Int" or coefficients or premises):
            raise ReconstructionError("cut th-lemma requires an Int certificate, no premises, and no coefficients "
                                      "at node %d" % node)
        for premise in premises:
            _atom_constraint(graph, premise)
        for literal in literals:
            _linear_constraint(graph, literal)
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
            parameters[0] == "bound" and graph.numeric == "Int" and bound_combination_refutes(constraints)):
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
    remaining = {terms[lit] for pos, lit in enumerate(literals)
                 if pos not in eliminations and graph.kind(lit) != z3.Z3_OP_FALSE}
    if len(conclusion) > 1 and remaining == {terms[graph.conclusion(node)]}:
        conclusion = (graph.conclusion(node),)
    positions = {}
    for position, literal in enumerate(conclusion):
        if graph.kind(literal) != z3.Z3_OP_FALSE:
            positions.setdefault(terms[literal], position)
    if remaining != set(positions):
        raise ReconstructionError("incorrect unit-resolution conclusion at node %d" % node)

    def refutation(position):
        """A proof of the negation of an eliminated or false literal, else None."""
        if position in eliminations:
            unit, negated_unit = eliminations[position]
            return "_step_%d" % unit if negated_unit else "(fun _literal => _literal _step_%d)" % unit
        if graph.kind(literals[position]) == z3.Z3_OP_FALSE:
            return "(fun _literal => _literal)"
        return None

    def branch(position, value):
        literal = literals[position]
        if position in eliminations:
            unit, negated_unit = eliminations[position]
            contradiction = ("(_step_%d %s)" % (unit, value) if negated_unit
                             else "(%s _step_%d)" % (value, unit))
            return "(False.elim %s)" % contradiction
        if graph.kind(literal) == z3.Z3_OP_FALSE:
            return "(False.elim %s)" % value
        return _inject(positions[terms[literal]], len(conclusion), value)

    if not literals:
        return "(False.elim _step_%d)" % first
    # Eliminated literals are cut off the clause by field notation,
    # `(h.resolve_left n)` (Or.resolve_left), which elaborates inside out from
    # the known type of the clause; only kept literals open an Or.elim case
    # split. One nested Or.elim per literal created metavariables at every
    # level and made a unit resolution over a 260-literal clause take seconds.
    subject, cases = "_step_%d" % first, []
    for position in range(len(literals) - 1):
        negation = refutation(position)
        if negation is not None:
            subject = "(%s.resolve_left %s)" % (subject, negation)
            continue
        cases.append("(Or.elim %s (fun _literal => %s) (fun _tail => " % (subject, branch(position, "_literal")))
        subject = "_tail"
    return "".join(cases) + branch(len(literals) - 1, subject) + "))" * len(cases)


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
    for hypothesis in hypotheses:
        for position, literal in enumerate(literals):
            negated_literal = "(fun _literal => _not_clause %s)" % (
                _inject(position, len(literals), "_literal"))
            if (graph.kind(hypothesis) == z3.Z3_OP_NOT
                    and terms[graph.arguments(hypothesis)[0]] == terms[literal]):
                arguments.append(negated_literal)
                break
            if (graph.kind(literal) == z3.Z3_OP_NOT
                    and terms[graph.arguments(literal)[0]] == terms[hypothesis]):
                arguments.append("(@Decidable.byContradiction %s _df%d %s)" % (
                    _formula(graph, hypothesis), hypothesis, negated_literal))
                decidable.add(hypothesis)
                break
        else:
            raise ReconstructionError("lemma does not discharge every hypothesis at node %d" % node)
    contradiction = "(_step_%d %s)" % (premise, " ".join(arguments))
    return ("(@Decidable.byContradiction %s _df%d (fun _not_clause => %s))" % (
        _formula(graph, conclusion), conclusion, contradiction)), decidable


def _outline_boundaries(graph):
    """Return the steps checked as separate lemmas: shared subproofs and chunk ends.

    A subproof used by several steps is checked once. A long chain without
    sharing is cut whenever a step would otherwise nest more than
    _OUTLINE_CHUNK_STEPS steps, so each lemma stays within the elaborator's
    default heartbeat budget. Only steps the root uses are outlined; the log
    may record derivations the refutation never needs. Arguments precede
    their node, so one increasing pass sees every premise's final size before
    its consumer.
    """
    reachable, pending = set(), [graph.proof]
    while pending:
        node = pending.pop()
        if node not in reachable:
            reachable.add(node)
            pending.extend(graph.arguments(node)[:-1])
    uses = Counter(premise for node in reachable for premise in graph.arguments(node)[:-1])
    boundaries = {node for node in reachable if uses[node] > 1} | {graph.proof}
    size = {}
    for node in sorted(reachable):
        total = 1
        for premise in graph.arguments(node)[:-1]:
            if premise in boundaries:
                continue
            if total + size[premise] > _OUTLINE_CHUNK_STEPS:
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


def _outline_steps(graph, steps, dependencies, signature, tails):
    """Check proof subgraphs separately instead of one enormous nested term.

    Returns the Lean lines and the decidability witnesses the root lemma takes
    as parameters. The arithmetic and uninterpreted slices already report the
    standard axioms, so their lemmas take classical witnesses locally; the
    propositional slice stays axiom-free by receiving every witness as a
    parameter that the main theorem introduces constructively. Each lemma
    binds the conjunction tails its and-elims start from (tails, see
    _and_elim) after the premise they project.
    """
    classical = bool(graph.arithmetic or graph.uninterpreted)
    boundaries = _outline_boundaries(graph)
    inputs = _balanced("And", [_formula(graph, node) for node in graph.assertions], "True")
    lines = ["", "private def Inputs %s : Prop := %s" % (signature, inputs)]
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
        body = [line for node in sorted(local) for line in steps[node] + _tail_lets(node, needed.get(node, 0))]
        decidable = set(re.findall(r"\b_df?\d+\b", "\n".join(body)))
        if not classical:
            for node in external:
                decidable.update(witnesses[node])
        witnesses[root] = sorted(decidable, key=_witness_key)
        result = _formula(graph, graph.conclusion(root))
        for hypothesis in reversed(dependencies[root]):
            result = "(%s -> %s)" % (_formula(graph, hypothesis), result)
        lines.extend([
            "",
            "private theorem proof_step_%d %s" % (root, signature),
            "    (_inputs : Inputs _atoms%s)" % graph.valuation,
        ])
        if classical:
            lines.append("    : %s :=" % result)
            for name in witnesses[root]:
                formula = _witness_formula(graph, name)
                lines.append("  let %s : Decidable %s := Classical.propDecidable %s" % (name, formula, formula))
        else:
            lines.extend("    (%s : Decidable %s)" % (name, _witness_formula(graph, name))
                         for name in witnesses[root])
            lines.append("    : %s :=" % result)
        for node in sorted(external):
            arguments = "" if classical else "".join(" " + name for name in witnesses[node])
            lines.append("  let _step_%d := proof_step_%d _atoms%s _inputs%s" % (
                node, node, graph.valuation, arguments))
            lines.extend(_tail_lets(node, needed.get(node, 0)))
        lines.extend(body)
        lines.append("  _step_%d" % root)
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
                        **indices["numeric_functions"]}
    digest = hashlib.sha256(source.encode("utf-8")).hexdigest()
    namespace = "Z3Proofs.NativeCertificate.p" + digest
    lines = ["import Init", "", "-- Original input SHA-256: " + digest]
    if queries > 1:
        # The theorem is about one query of an incremental script: the
        # assertions in scope at that check-sat, with its assumptions.
        lines.append("-- Certified query: check-sat %d of %d (zero-based index %d); the assertions below are "
                     "the ones in scope there, assumptions included." % (query + 1, queries, query))
    for table, label in _TABLE_LABELS.items():
        if table == "numeric_functions":
            label = label % graph.numeric
        for name, decl in sorted(tables[table].items(), key=lambda item: indices[table][item[1]]):
            lines.append("-- %s %d: %s" % (label, indices[table][decl], json.dumps(name, ensure_ascii=True)))
    if graph.arithmetic and graph.numeric == "Int":
        lines.append("-- Int variables are encoded as Int; the integer lemmas are proved by omega, else grind.")
        if any(decl.kind in _INT_NAMES for decl in graph.declarations):
            lines.append("-- Int div and mod by a numeral are Lean's Euclidean / and %; abs is the ite SMT-LIB defines.")
        if any(decl.kind == z3.Z3_OP_REM for decl in graph.declarations):
            lines.append("-- Int rem by a numeral k is Z3's (ite (>= k 0) (mod t k) (- (mod t k))): t % k, or -(t % k) for k < 0.")
    elif graph.arithmetic:
        lines.append("-- Real variables are encoded as Rat; see the exporter documentation.")
        if any(decl.kind in _NUMERIC_KINDS for decl in graph.declarations):
            lines.append("-- Real abs, which Z3 accepts beyond SMT-LIB, is the ite (if t >= 0 then t else -t).")
    if graph.arithmetic and graph.uninterpreted:
        lines.append("-- %s arguments of functions and predicates are injected into _m.U by %s;"
                     " functions with %s result are the family %s." % (
                         graph.numeric, graph.injection, {"Real": "a Real", "Int": "an Int"}[graph.numeric],
                         graph.numeric_functions))
    if len(graph.sorts) == 1:
        lines.append("-- Uninterpreted sort %s is the type _m.U; functions and predicates take argument lists."
                     % json.dumps(graph.sorts[0], ensure_ascii=True))
    elif graph.sorts:
        # One carrier for every sort is sound: a many-sorted model is an instance
        # of the theorem over the disjoint union of its carriers.
        lines.append("-- Uninterpreted sorts %s are the one type _m.U; functions and predicates take argument lists."
                     % ", ".join(json.dumps(sort, ensure_ascii=True) for sort in graph.sorts))
    elif graph.uninterpreted:
        lines.append("-- No uninterpreted sort: the type _m.U carries only the Boolean arguments of the predicates.")
    if any(decl.kind == z3.Z3_OP_UNINTERPRETED and "Bool" in decl.domain for decl in graph.declarations):
        lines.append("-- Boolean arguments of functions and predicates are injected into _m.U by _m.bool.")
    # Formulas over wide n-ary connectives render as right-nested And/Or chains
    # and long refutations nest hundreds of let-bound steps; every declaration
    # (definitions, lemmas, proof steps, the theorem) elaborates under a raised
    # recursion limit, scoped to this namespace. This is not a trust setting.
    lines.extend(["namespace " + namespace, "", "set_option maxRecDepth 100000", ""])
    options = len(lines) - 1
    lines.extend(_interpretation_structure(graph))
    signature = "(_atoms : Nat -> Prop)" + _valuation_binder(graph)
    classical = set()  # Term nodes containing an ite or abs: their classical instance is noncomputable.
    for node in range(len(graph.nodes)):
        if graph.is_term(node):
            if graph.kind(node) in (z3.Z3_OP_ITE, z3.Z3_OP_ABS) or any(arg in classical for arg in graph.arguments(node)):
                classical.add(node)
            lines.append("%sdef term_%d %s : %s := %s" % (
                "noncomputable " if node in classical else "", node, signature,
                graph.number_type if graph.is_arith(node) else "_m.U", _term_body(graph, node, variable_indices)))
        elif graph.decl(node).range == "Bool":
            lines.append("def formula_%d %s : Prop := %s" % (
                node, signature, _formula_body(graph, node, atom_indices)))
    rewrites, def_axioms, th_lemmas, decidable_atoms, decidable_formulas = {}, {}, {}, set(), set()
    for node in range(len(graph.nodes)):
        if graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA:
            _check_th_lemma(graph, node)
            if graph.decl(node).parameters[0] == "cnf":
                lemma, term = _cnf_lemma(graph, node, atom_indices, variable_indices)
            else:
                lemma, term = _grind_lemma(graph, node, "th_lemma", atom_indices, variable_indices,
                                           opaque_tactic=_opaque_tactic(graph, node),
                                           structural=(_farkas_combination(graph, node)
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
    steps = []
    step_blocks = {}
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
            term = _resolution(graph, terms, node)
        else:
            raise ReconstructionError("unsupported native proof rule: %s" % graph.decl(node).name)
        # Abstract open DAG nodes so shared subproofs can be discharged independently.
        parameters = "".join(" (_hyp%d : %s)" % (hypothesis, _formula(graph, hypothesis))
                             for hypothesis in dependencies[node])
        begin = len(steps)
        steps.append("  let _step_%d%s : %s :=" % (node, parameters, _formula(graph, conclusion)))
        if graph.kind(node) != z3.Z3_OP_PR_LEMMA:
            for premise in dict.fromkeys(premises):
                if dependencies[premise]:
                    arguments = "".join(" _hyp%d" % hypothesis for hypothesis in dependencies[premise])
                    steps.append("    let _step_%d := _step_%d%s" % (premise, premise, arguments))
        steps.append("    " + term)
        step_blocks[node] = steps[begin:]
    if dependencies[graph.proof]:
        raise ReconstructionError("the root proof has undischarged hypotheses")
    if ite_congruence:
        lines.extend(_ITE_CONGRUENCE)
    witnesses = []
    if outline:
        outlined, witnesses = _outline_steps(graph, step_blocks, dependencies, signature, tails)
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
        lines.append("  proof_step_%d _atoms%s %s%s" % (
            graph.proof, graph.valuation, inputs, "".join(" " + name for name in witnesses)))
    else:
        for atom in sorted(decidable_atoms):
            lines.append("  refute_with_decidable (_atoms %d) fun _d%d =>" % (atom, atom))
        for formula in sorted(decidable_formulas):
            lines.append("  refute_with_decidable %s fun _df%d =>" % (_formula(graph, formula), formula))
        needed = _needed_tails(tails, step_blocks)
        for node, block in step_blocks.items():
            lines.extend(block + _tail_lets(node, needed.get(node, 0)))
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
