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
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import z3

from proof_certificate import (
    ProofExportError, bound_combination_refutes, integer_tightened, is_uninterpreted_sort,
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
# _integer_divisor), abs is the ite SMT-LIB defines it as. All three are
# opaque atoms of the linear forms; omega reads / and % by a positive
# numeral and grind proves the axioms of a negative divisor.
_INT_NAMES = {z3.Z3_OP_IDIV: "div", z3.Z3_OP_MOD: "mod", z3.Z3_OP_ABS: "abs"}
_INT_ARITY = {z3.Z3_OP_IDIV: 2, z3.Z3_OP_MOD: 2, z3.Z3_OP_ABS: 1}
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
# sat.smt arithmetic solver's own axioms (the div and mod definitions), a
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
_NORMALIZED_REWRITE_ATOMS = 16
# Propagation steps and atom splits a propositional rewrite's direct proof may
# take, and characters its typed `have` steps may render, before the truth
# table is used instead (see _PropositionalProver). A term of one million
# characters checks in a few seconds; a parity rewrite over seven atoms
# renders 2.8 MB and exceeds Lean's heartbeat limit.
_STRUCTURAL_REWRITE_STEPS = 20000
_STRUCTURAL_REWRITE_CHARS = 1000000
_RESERVED_SORTS = ("Bool", "Real", "Int", "Proof")
# The uninterpreted sorts are one type variable; constants, functions, and
# predicates are indexed families over argument lists, so one signature serves
# every arity and every sort. Quantifying over all such interpretations covers
# every model: a many-sorted model is one instance with the disjoint union of
# its carriers as _U, since every ground term keeps its sort and equality is
# only ever stated between terms of one sort (the certificate keeps the sort
# names, and the proof graph is checked to be well-sorted before rendering).
# A Boolean argument of a function or predicate is injected into _U by the
# quantified map _bool, so Bool is treated as one more sort: a model's Bool
# carrier joins the disjoint union and _bool picks its two values. Nothing
# asserts that _bool True and _bool False differ, and nothing needs to: euf
# lemmas only use the congruence p = q -> _bool p = _bool q.
_UF_BINDERS = (" (_U : Type) (_elems : Nat -> _U) (_funs : Nat -> List _U -> _U) (_preds : Nat -> List _U -> Prop)"
               " (_bool : Prop -> _U)")
_UF_ARGUMENTS = " _U _elems _funs _preds _bool"
# QF_UFLRA: the Rat valuation of the Real variables next to the carrier. A
# Real argument of a function or predicate is injected into _U by _real, as a
# Boolean one is by _bool (Real joins the disjoint union as one more carrier),
# and a function with a Real result is one more indexed family _rfuns whose
# applications are the opaque atoms of the linear forms, as in Z3's arithmetic
# solver. Nothing states that _real is injective and nothing needs it: euf
# lemmas only use the congruence x = y -> _real x = _real y. QF_UFLIA is the
# same encoding over Int, with the injection _int and the family _ifuns.
_UFLRA_BINDERS = " (_vars : Nat -> Rat)" + _UF_BINDERS + " (_real : Rat -> _U) (_rfuns : Nat -> List _U -> Rat)"
_UFLRA_ARGUMENTS = " _vars" + _UF_ARGUMENTS + " _real _rfuns"
_UFLIA_BINDERS = " (_vars : Nat -> Int)" + _UF_BINDERS + " (_int : Int -> _U) (_ifuns : Nat -> List _U -> Int)"
_UFLIA_ARGUMENTS = " _vars" + _UF_ARGUMENTS + " _int _ifuns"
# The injection of a numeric argument into the carrier and the family of
# functions with a numeric result, by arithmetic sort.
_INJECTIONS = {"Real": "_real", "Int": "_int"}
_NUMERIC_FUNCTIONS = {"Real": "_rfuns", "Int": "_ifuns"}
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
            if _INT_NAMES[kind] != name or numeric != "Int":
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
    # The theorem states the assertions, so every div and mod they contain
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
        if graph.kind(index) in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD):
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
    sorts never compare equal even though Lean renders every sort as _U.
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


def _infix(operator, arguments):
    result = arguments[0]
    for argument in arguments[1:]:
        result = "(%s %s %s)" % (result, operator, argument)
    return result


def _application_arguments(graph, arguments, term, formula):
    """Render the argument list of a function or predicate over the uninterpreted sorts.

    A Boolean argument is injected into the carrier by _bool (its formula is
    rendered as a Prop) and a Real or Int one by _real or _int.
    """
    return "[%s]" % ", ".join("(%s %s)" % (graph.injection, term(arg)) if graph.is_arith(arg)
                              else term(arg) if graph.is_term(arg)
                              else "(_bool %s)" % formula(arg) for arg in arguments)


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
            return ("_vars %d" if graph.is_arith(node) else "_elems %d") % index
        return "%s %d %s" % (graph.numeric_functions if graph.is_arith(node) else "_funs", index,
                             _application_arguments(graph, arguments, term, formula))
    if kind == z3.Z3_OP_ANUM:
        return _numeral(graph, Fraction(graph.decl(node).name))
    if kind == z3.Z3_OP_ITE:
        # The instance's proposition is inferred from the condition.
        return "(@ite %s %s (Classical.propDecidable _) %s %s)" % (
            graph.number_type if graph.is_arith(node) else "_U",
            formula(arguments[0]), term(arguments[1]), term(arguments[2]))
    args = [term(arg) for arg in arguments]
    if kind == z3.Z3_OP_UMINUS:
        return "(-%s)" % args[0]
    if kind == z3.Z3_OP_ABS:
        # SMT-LIB's definition; the instance's proposition is inferred from the condition.
        return "(@ite Int (%s >= ((0 : Int))) (Classical.propDecidable _) %s (-%s))" % (args[0], args[0], args[0])
    if kind in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD):
        return "(%s %s %s)" % (args[0], "/" if kind == z3.Z3_OP_IDIV else "%", args[1])
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
        return "_preds %d %s" % (atom_indices[graph.nodes[node].declaration],
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
    injected by _bool, so its equivalence becomes an equality by propext.
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
        elements = ["(congrArg _bool (propext %s))" % argument if not graph.is_term(first)
                    else "(congrArg %s %s)" % (graph.injection, argument) if graph.is_arith(first) else argument
                    for first, argument in zip(left_args, arguments)]
        if graph.is_term(left):
            return "(congrArg (%s %d) %s)" % (graph.numeric_functions if graph.is_arith(left) else "_funs",
                                              variable_indices[graph.nodes[left].declaration],
                                              _list_congruence(elements)), False, []
        return "(Iff.of_eq (congrArg (_preds %d) %s))" % (atom_indices[graph.nodes[left].declaration],
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


def _and_elim(graph, terms, node):
    premise, conclusion = graph.arguments(node)
    conjunction = graph.conclusion(premise)
    if graph.kind(conjunction) != z3.Z3_OP_AND:
        raise ReconstructionError("and-elim requires a conjunction at node %d" % node)
    arguments = graph.arguments(conjunction)
    for position, argument in enumerate(arguments):
        if terms[argument] == terms[conclusion]:
            return _select(position, len(arguments), "_step_%d" % premise)
    raise ReconstructionError("and-elim conclusion is not a conjunct at node %d" % node)


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
        pending.extend(graph.arguments(formula))
    return reachable, theory


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


def _grind_lemma(graph, node, prefix, atom_indices, variable_indices):
    """Prove a conclusion over theory atoms with grind after unfolding its definitions.

    grind decides linear arithmetic over ordered fields, congruence closure
    over uninterpreted functions, and propositional structure; the Lean kernel
    checks the proof it produces. Lean core's Rat library already depends on
    the standard axioms, so arithmetic lemmas do too. A step with premises
    (the legacy core's th-lemma and arithmetic monotonicity) is stated as the
    implication from the premise conclusions and applied to their steps.
    """
    conclusion = graph.conclusion(node)
    premises = graph.arguments(node)[:-1]
    reachable, _ = _reachable(graph, conclusion)
    for premise in premises:
        reachable |= _reachable(graph, graph.conclusion(premise))[0]
    definitions = ["%s_%d" % ("term" if graph.is_term(formula) else "formula", formula)
                   for formula in sorted(reachable, reverse=True)]
    statement = " -> ".join([_formula(graph, graph.conclusion(premise)) for premise in premises]
                            + [_formula(graph, conclusion)])
    lines = [
        "",
        "set_option maxHeartbeats 1000000 in",
        "private theorem %s_%d (_atoms : Nat -> Prop)%s" % (prefix, node, _valuation_binder(graph)),
        "    : %s := by" % statement,
        "  unfold " + " ".join(definitions),
    ]
    if graph.arithmetic:
        lines.extend(_scaling_helpers(graph, reachable, atom_indices, variable_indices))
        lines.extend(_ite_gate_helpers(graph, reachable, atom_indices, variable_indices))
    if graph.uninterpreted:
        lines.extend(_boolean_argument_helpers(graph, reachable, atom_indices, variable_indices))
    if graph.arithmetic and graph.uninterpreted:
        lines.extend(_real_argument_helpers(graph, reachable, atom_indices, variable_indices))
    lines.append("  " + _theory_tactic(graph))
    return lines, "(%s_%d _atoms%s%s)" % (prefix, node, graph.valuation,
                                          "".join(" _step_%d" % premise for premise in premises))


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
    from either case it derives _bool p = _bool True or _bool p = _bool False
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
    normal form of the same ite. Every pair of reachable numeric arguments
    with one normal form (_real_argument_key) gets an explicit equality,
    which the theory tactic proves on its own (splitting the ite conditions)
    and grind then uses for congruence.
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
    is a linear atom is keyed by the canonical polarity of that condition
    (the non-strict comparison, swapping the branches when the condition is
    the strict complement) and by the keys of its branches. Two terms with
    one key denote the same value, which grind proves and the helper states.
    """
    terms = {}
    constant = _linear_term(graph, node, Fraction(1), terms)
    atoms = [(_real_atom_key(graph, atom), value) for atom, value in terms.items() if value != 0]
    return (tuple(sorted(atoms, key=repr)), constant)


def _real_atom_key(graph, atom):
    if graph.kind(atom) != z3.Z3_OP_ITE:
        return ("atom", atom)
    condition, then_branch, else_branch = graph.arguments(atom)
    try:
        relation, terms, constant = _polarity_constraint(graph, condition, True)
    except ReconstructionError:
        return ("atom", atom)  # a condition that is no linear atom: opaque
    if relation == "<":
        relation, constant = "<=", -constant
        terms = {variable: -value for variable, value in terms.items()}
        then_branch, else_branch = else_branch, then_branch
    condition_key = (relation, tuple(sorted(((_real_atom_key(graph, variable), value)
                                              for variable, value in terms.items()), key=repr)), constant)
    return ("ite", condition_key, _real_argument_key(graph, then_branch), _real_argument_key(graph, else_branch))


def _boolean_structure(graph, node, atom_indices, memo=None):
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
    """
    memo = {} if memo is None else memo
    if node in memo:
        return memo[node]
    kind, arguments = graph.kind(node), graph.arguments(node)
    if kind == z3.Z3_OP_UNINTERPRETED and not arguments:
        structure = ("atom", atom_indices[graph.nodes[node].declaration])
    else:
        children = [_boolean_structure(graph, argument, atom_indices, memo) for argument in arguments]
        structure = _boolean_connective(kind, children)
    memo[node] = structure
    return structure


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
    """Render a structure as the Lean proposition the unfolded definitions reduce to."""
    kind = structure[0]
    if kind == "atom":
        return "(_atoms %d)" % structure[1]
    if kind == "true":
        return "True"
    if kind == "false":
        return "False"
    children = [_render_structure(child) for child in _structure_children(structure)]
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
    """Apply one handler per disjunct of a right-nested disjunction proof."""
    result = handlers[-1]
    for handler in reversed(handlers[:-1]):
        result = "(fun _tail => Or.elim _tail %s %s)" % (handler, result)
    return "(%s %s)" % (result, proof)


class _PropositionalProver:
    """Prove a propositional equivalence by a direct Lean term, without a truth table.

    The two sides are gates over shared atoms. A direction is proved by
    assuming one side, propagating truth values through the gates (each
    propagation step is a typed `have` whose proof uses only the immediate
    operands, as in _gate_contradiction), and, while propagation alone does
    not settle the other side, splitting on an atom with Decidable.em; a
    branch ends with the other side proved or with a contradiction. Double
    negations are cancelled by Decidable.byContradiction on atoms only, so
    the term needs no decidability instance for a compound formula, and only
    the atoms whose decidability it uses become instance parameters of the
    lemma. The term is free of axioms. A direction not settled within
    _STRUCTURAL_REWRITE_STEPS steps or _STRUCTURAL_REWRITE_CHARS rendered
    characters (each `have` states its full proposition, so a term can be
    large after few steps), or whose splits reach a satisfying assignment
    (the equivalence does not hold), returns None and the caller falls back
    to the truth table; Lean checks the term as it checks any other, so a
    wrong term is rejected, never trusted.
    """

    def __init__(self, left, right):
        self.parents = {}
        self.needed = set()
        self.names = set()
        self.fresh = 0
        self.steps = 0
        self.chars = 0
        for root in (left, right):
            self._index(root)
        self.constants = [(structure, structure[0] == "true", "True.intro" if structure[0] == "true"
                           else "(fun _absurd => _absurd)")
                          for structure in (("true",), ("false",)) if structure in self.parents]

    def _index(self, structure):
        if structure in self.parents:
            return
        self.parents[structure] = {}
        for child in _structure_children(structure):
            self._index(child)
            self.parents[child][structure] = None

    def _name(self):
        self.fresh += 1
        self.names.add("_f%d" % self.fresh)
        return "_f%d" % self.fresh

    def _exhausted(self):
        return self.steps > _STRUCTURAL_REWRITE_STEPS or self.chars > _STRUCTURAL_REWRITE_CHARS

    def equivalence(self, left, right):
        forward = self.implication(left, right)
        backward = self.implication(right, left) if forward is not None else None
        if backward is None:
            return None
        return "(Iff.intro %s %s)" % (forward, backward)

    def implication(self, source, target):
        """A term of type source -> target, or None."""
        hypothesis = self._name()
        body = self._prove(dict(), target, self.constants + [(source, True, hypothesis)])
        if body is None:
            return None
        return "(fun (%s : %s) => (%s : %s))" % (
            hypothesis, _render_structure(source), body, _render_structure(target))

    def _prove(self, state, target, facts):
        """A term of type target under the state extended by the facts, or None."""
        lines, pending = [], []
        conflict = None
        for structure, truth, proof in facts:
            conflict = conflict or self._assign(state, lines, pending, structure, truth, proof)
        conflict = conflict or self._propagate(state, lines, pending)
        if conflict is not None:
            return self._block(lines, "(False.elim %s)" % conflict)
        if target in state and state[target][0]:
            return self._block(lines, state[target][1])
        atoms = sorted((-len(self.parents[atom]), atom[1]) for atom in self.parents
                       if atom[0] == "atom" and atom not in state)
        self.steps += 1
        if not atoms or self._exhausted():
            return None  # every atom assigned without the target holding: the equivalence does not hold
        atom = ("atom", atoms[0][1])
        self.needed.add(atom[1])
        branches = []
        for value in (True, False):
            name = self._name()
            branch = self._prove(dict(state), target, [(atom, value, name)])
            if branch is None:
                return None
            branches.append("(fun %s => %s)" % (name, branch))
        return self._block(lines, "(Or.elim (Decidable.em (_atoms %d)) %s %s)" % ((atom[1],) + tuple(branches)))

    @staticmethod
    def _block(lines, body):
        return "(%s %s)" % (" ".join(lines), body) if lines else body

    def _assign(self, state, lines, pending, structure, truth, proof, decides=None):
        """Record a truth value with its proof; return a proof of False if it contradicts the state.

        A value already recorded with the same truth is left alone and its
        proof is dropped; `decides` names the atom whose decidability the
        proof uses, recorded as needed only when the proof is kept.
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
            name = self._name()
            rendered = _render_structure(structure)
            line = "have %s : %s := %s;" % (name, rendered if truth else "(Not %s)" % rendered, proof)
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
            for target, truth, proof, decides in self._consequences(state, structure):
                conflict = self._assign(state, lines, pending, target, truth, proof, decides)
                if conflict is not None:
                    return conflict
        return None

    def _consequences(self, state, structure):
        """The truth values one gate determines from its own value and its operands' values.

        Each consequence is (structure, truth, proof, decides) where decides
        is the atom whose Decidable instance the proof uses, or None.
        """
        kind = structure[0]
        children = _structure_children(structure)
        value = state.get(structure)
        values = [state.get(child) for child in children]
        truths = [None if v is None else v[0] for v in values]
        proofs = [None if v is None else v[1] for v in values]
        count = len(children)
        out = []

        def add(target, truth, proof, decides=None):
            out.append((target, truth, proof, decides))

        if kind == "not":
            (child,), (truth,), (proof,) = children, truths, proofs
            if value is not None:
                if value[0]:
                    add(child, False, value[1])
                elif child[0] == "atom":
                    add(child, True, "(Decidable.byContradiction (fun _g => %s _g))" % value[1], child[1])
            if truth is True:
                add(structure, False, "(fun _g => _g %s)" % proof)
            elif truth is False:
                add(structure, True, proof)
        elif kind == "and":
            if value is not None and value[0]:
                for i, child in enumerate(children):
                    add(child, True, _project(i, count, value[1]))
            if value is not None and not value[0] and truths.count(None) == 1 and False not in truths:
                position = truths.index(None)
                parts = ["_g" if i == position else proof for i, proof in enumerate(proofs)]
                add(children[position], False,
                    "(fun _g => %s %s)" % (value[1], _fold("And.intro", parts, "True.intro")))
            if False in truths:
                position = truths.index(False)
                add(structure, False,
                    "(fun _g => %s %s)" % (proofs[position], _project(position, count, "_g")))
            elif None not in truths:
                add(structure, True, _fold("And.intro", proofs, "True.intro"))
        elif kind == "or":
            if value is not None and not value[0]:
                for i, child in enumerate(children):
                    add(child, False, "(fun _g => %s %s)" % (value[1], _inject(i, count, "_g")))
            if value is not None and value[0] and truths.count(None) == 1 and True not in truths:
                position = truths.index(None)
                handlers = ["(fun _g => _g)" if i == position else "(fun _g => absurd _g %s)" % proof
                            for i, proof in enumerate(proofs)]
                add(children[position], True, _eliminate_or(value[1], handlers))
            if True in truths:
                position = truths.index(True)
                add(structure, True, _inject(position, count, proofs[position]))
            elif None not in truths:
                add(structure, False, "(fun _g => %s)" % _eliminate_or("_g", proofs))
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
                if antecedent[0] == "atom":
                    add(antecedent, True, "(Decidable.byContradiction (fun _g => %s (fun _h => absurd _h _g)))"
                        % value[1], antecedent[1])
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
                elif truth_a is False and right[0] == "atom":
                    add(right, True, "(Decidable.byContradiction (fun _g => %s (Iff.intro "
                        "(fun _h => absurd _h %s) (fun _h => absurd _h _g))))" % (value[1], proof_a), right[1])
                if truth_b is True:
                    add(left, False, "(fun _g => %s (Iff.intro (fun _ => %s) (fun _ => _g)))"
                        % (value[1], proof_b))
                elif truth_b is False and left[0] == "atom":
                    add(left, True, "(Decidable.byContradiction (fun _g => %s (Iff.intro "
                        "(fun _h => absurd _h _g) (fun _h => absurd _h %s))))" % (value[1], proof_b), left[1])
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


def _structural_equivalence(graph, left, right, atom_indices):
    """A direct Lean term proving the Boolean equivalence of two formulas, with the atoms it needs decidable."""
    memo = {}
    left, right = (_boolean_structure(graph, side, atom_indices, memo) for side in (left, right))
    prover = _PropositionalProver(left, right)
    return prover.equivalence(left, right), sorted(prover.needed)


def _rewrite_lemma(graph, node, atom_indices, variable_indices=None, terms=None):
    """Generate a Lean lemma for a rewrite step, checked independently of the assertions.

    A propositional rewrite is proved by a direct term from gate propagation
    and case splits on atoms (_PropositionalProver); the exhaustive truth
    table over the atoms' decidability witnesses, exponential in their number,
    is the fallback when the prover gives up. Theory rewrites go to grind,
    except that a rewrite between two identical formulas (the legacy core
    records one per assertion) is Iff.refl.
    """
    conclusion = graph.conclusion(node)
    left, right = _equivalence(graph, conclusion, "rewrite")
    reachable, theory = _reachable(graph, conclusion)
    if theory and terms is not None and terms[left] == terms[right]:
        return [], set(), "(%s.refl %s)" % (_relation(graph, left), _side(graph, left))
    if graph.is_term(left):
        # A rewrite between terms (the legacy core simplifies ite terms, for
        # example (ite true a b) to a): a theory tautology for grind.
        lines, term = _grind_lemma(graph, node, "rewrite", atom_indices, variable_indices)
        return lines, set(), term
    if theory:
        atoms = [formula for formula in sorted(reachable)
                 if graph.kind(formula) in _ARITH_PREDICATE_NAMES.keys() | {z3.Z3_OP_EQ}
                 and graph.arguments(formula) and graph.is_arith(graph.arguments(formula)[0])]
        distinct = any(graph.kind(formula) == z3.Z3_OP_DISTINCT for formula in reachable)
        if len(atoms) > _NORMALIZED_REWRITE_ATOMS and not distinct and _linear_over_variables(graph, atoms):
            lines, term = _normalized_rewrite(graph, node, reachable, atoms, atom_indices, variable_indices)
        else:
            lines, term = _grind_lemma(graph, node, "rewrite", atom_indices, variable_indices)
        return lines, set(), term
    proof, atoms = _structural_equivalence(graph, left, right, atom_indices)
    if proof is None:
        atoms = sorted(atom_indices[graph.nodes[formula].declaration]
                       for formula in reachable if graph.kind(formula) == z3.Z3_OP_UNINTERPRETED)
    lines = ["", "private theorem rewrite_%d (_atoms : Nat -> Prop)%s" % (node, _valuation_binder(graph))]
    for atom in atoms:
        lines.append("    [_d%d : Decidable (_atoms %d)]" % (atom, atom))
    lines.extend([
        "    : %s := by" % _formula(graph, conclusion),
        "  unfold " + " ".join("formula_%d" % formula for formula in sorted(reachable, reverse=True)),
    ])
    if proof is not None:
        lines.append("  exact " + proof)
        term = "(@rewrite_%d _atoms%s%s)" % (node, graph.valuation, "".join(" _d%d" % atom for atom in atoms))
        return lines, atoms, term
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


def _linear_over_variables(graph, atoms):
    """Whether the linear forms of the atoms range over Real variables alone.

    _normalized_rewrite identifies the atoms of a linear form by variable
    index; an opaque ite term or function application has none.
    """
    return all(graph.kind(variable) == z3.Z3_OP_UNINTERPRETED and not graph.arguments(variable)
               for atom in atoms for variable in _atom_constraint(graph, atom)[1])


def _normalized_rewrite(graph, node, reachable, atoms, atom_indices, variable_indices):
    """Separate linear atom normalization from propositional rewrite search."""
    def numeral(value):
        return _numeral(graph, value)

    canonical, normalized_atoms, rewrites, lines = {}, {}, [], [
        "", "set_option maxHeartbeats 1000000 in",
        "set_option linter.unnecessarySimpa false in",
        "private theorem rewrite_%d (_atoms : Nat -> Prop)%s" % (node, _valuation_binder(graph)),
        "    : %s := by" % _formula(graph, graph.conclusion(node)),
    ]
    for atom in atoms:
        relation, terms, constant = _atom_constraint(graph, atom)
        negated = relation == "<"
        if negated:
            terms, constant, relation = {var: -value for var, value in terms.items()}, -constant, "<="
        first = min(terms, key=lambda var: variable_indices[graph.nodes[var].declaration]) if terms else None
        if graph.numeric == "Int" and relation == "<=" and terms and terms[first] < 0:
            # Over Int every atom is already tightened to t <= 0, whose
            # complement is -t + 1 <= 0: key the row with a negative leading
            # coefficient as the negation of its complement, so that (< x 5)
            # and (>= x 5) share one atom (the replay's _Normalizer does the
            # same) and the propositional lemma sees them as complementary.
            terms, constant, negated = {var: -value for var, value in terms.items()}, -constant + 1, True
        if terms:
            scale = terms[first] if relation == "=" else abs(terms[first])
            terms, constant = {var: value / scale for var, value in terms.items()}, constant / scale
        ordered = tuple(sorted((variable_indices[graph.nodes[var].declaration], value)
                               for var, value in terms.items()))
        key = relation, ordered, constant
        scale = 1
        for value in [value for _, value in ordered] + [constant]:
            scale = scale * value.denominator // _gcd(scale, value.denominator)
        parts = ["(%s * _vars %d)" % (numeral(value * scale), var) for var, value in ordered]
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
        lines.extend([
            "  have %s : %s <-> %s := by" % (rewrite, _formula(graph, atom), target),
            "    change %s <-> %s" % (_inline(graph, atom, atom_indices, variable_indices), expanded),
            "    grind",
        ])
    definitions = ["formula_%d" % formula for formula in sorted(reachable, reverse=True)
                   if not graph.is_arith(formula) and formula not in atoms]
    rendered = dict(normalized_atoms)

    def boolean(formula):
        if formula not in rendered:
            body = _formula_body(graph, formula, atom_indices)
            if graph.kind(formula) == z3.Z3_OP_UNINTERPRETED:
                body = "(" + body + ")"
            for arg in graph.arguments(formula):
                body = body.replace(_formula(graph, arg), boolean(arg))
            rendered[formula] = body
        return rendered[formula]

    names = list(canonical.values())
    structures = {}

    def structure(formula):
        if formula in structures:
            return structures[formula]
        kind = graph.kind(formula)
        if formula not in normalized_atoms and kind in (z3.Z3_OP_AND, z3.Z3_OP_OR):
            result = ("and" if kind == z3.Z3_OP_AND else "or",
                      tuple(structure(arg) for arg in graph.arguments(formula)))
        elif formula not in normalized_atoms and kind == z3.Z3_OP_NOT:
            result = ("not", structure(graph.arguments(formula)[0]))
        else:
            atom = normalized_atoms.get(formula)
            if atom is not None and atom.startswith("(Not ") and atom.endswith(")"):
                result = ("not", ("atom", atom[5:-1]))
            else:
                result = ("atom", boolean(formula))
        structures[formula] = result
        return result

    left, right = graph.arguments(graph.conclusion(node))
    forward = _propositional_implication(structure(left), structure(right))
    backward = _propositional_implication(structure(right), structure(left))
    boolean_lemma = [
        "", "set_option maxHeartbeats 1000000 in",
        "private theorem normalized_rewrite_%d (_atoms : Nat -> Prop)%s" % (
            node, "".join(" (%s : Prop)" % name for name in names)),
        "    : %s :=" % boolean(graph.conclusion(node)),
    ]
    if forward is not None and backward is not None:
        boolean_lemma.append("  Iff.intro %s %s" % (forward, backward))
    else:
        boolean_lemma.append("  by grind (splits := 64)")
    lines.append("  simpa only [%s] using (normalized_rewrite_%d _atoms %s)" % (
        ", ".join(definitions + rewrites), node, " ".join(names)))
    return boolean_lemma + lines, "(rewrite_%d _atoms%s)" % (node, graph.valuation)


def _propositional_implication(source, target):
    """Build an and/or implication by projection and case analysis, without enumerating atoms."""
    budget = 4096

    def prove(goal, facts):
        if goal in facts:
            return facts[goal]
        kind, args = goal
        if kind == "and":
            proofs = [prove(arg, facts) for arg in args]
            if all(proof is not None for proof in proofs):
                return _fold("And.intro", proofs, "True.intro")
        elif kind == "or":
            for position, arg in enumerate(args):
                proof = prove(arg, facts)
                if proof is not None:
                    return _inject(position, len(args), proof)
        elif args == "True":
            return "True.intro"
        return None

    def derive(pending, facts, depth):
        nonlocal budget
        budget -= 1
        if budget < 0:
            return None
        branches = []
        while pending:
            formula, proof = pending.pop()
            facts[formula] = proof
            kind, args = formula
            if kind == "and":
                pending.extend((arg, _project(i, len(args), proof)) for i, arg in enumerate(args))
            elif kind == "or":
                if not args:
                    return "(False.elim %s)" % proof
                branches.append((args, proof))
            elif args == "False":
                return "(False.elim %s)" % proof
        result = prove(target, facts)
        if result is not None:
            return result
        if not branches:
            return None
        args, proof = branches.pop()
        rest = [(("or", children), evidence) for children, evidence in branches]
        proofs = []
        for i, arg in enumerate(args):
            name = "_case%d_%d" % (depth, i)
            result = derive(rest + [(arg, name)], dict(facts), depth + 1)
            if result is None:
                return None
            proofs.append("(fun %s => %s)" % (name, result))
        result = proofs[-1]
        for branch in reversed(proofs[:-1]):
            result = "(fun _tail => Or.elim _tail %s %s)" % (branch, result)
        return "(%s %s)" % (result, proof)

    result = derive([(source, "_value")], {}, 0)
    return None if result is None else "(fun _value => %s)" % result


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

    Variables, ite terms, integer div and mod, and abs are the atoms of the
    linear form; each is opaque to Farkas reasoning, an ite tied to its
    branches by gate clauses and a div or mod to its operands by the
    solver's arith axioms.
    """
    kind = graph.kind(node)
    arguments = graph.arguments(node)
    if kind == z3.Z3_OP_ANUM:
        return scale * Fraction(graph.decl(node).name)
    if kind in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD):
        _integer_divisor(graph, node)
    if kind in (z3.Z3_OP_UNINTERPRETED, z3.Z3_OP_ITE, z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_ABS):
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
    """Return the nonzero constant divisor of an Int div or mod node, rejecting any other.

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
        # (the legacy core labels a lattice conflict farkas): the exporter
        # kept no coefficients because none certify the rounding, so only the
        # shape is checked (integer linear atoms, held premises included) and
        # Lean proves the clause or the implication.
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


def _outline_steps(graph, steps, dependencies, signature):
    """Check proof subgraphs separately instead of one enormous nested term.

    Returns the Lean lines and the decidability witnesses the root lemma takes
    as parameters. The arithmetic and uninterpreted slices already report the
    standard axioms, so their lemmas take classical witnesses locally; the
    propositional slice stays axiom-free by receiving every witness as a
    parameter that the main theorem introduces constructively.
    """
    classical = bool(graph.arithmetic or graph.uninterpreted)
    boundaries = _outline_boundaries(graph)
    inputs = _fold("And", [_formula(graph, node) for node in graph.assertions], "True")
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
        body = [line for node in sorted(local) for line in steps[node]]
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
    elif graph.arithmetic:
        lines.append("-- Real variables are encoded as Rat; see the exporter documentation.")
    if graph.arithmetic and graph.uninterpreted:
        lines.append("-- %s arguments of functions and predicates are injected into _U by %s;"
                     " functions with %s result are the family %s." % (
                         graph.numeric, graph.injection, {"Real": "a Real", "Int": "an Int"}[graph.numeric],
                         graph.numeric_functions))
    if len(graph.sorts) == 1:
        lines.append("-- Uninterpreted sort %s is the type _U; functions and predicates take argument lists."
                     % json.dumps(graph.sorts[0], ensure_ascii=True))
    elif graph.sorts:
        # One carrier for every sort is sound: a many-sorted model is an instance
        # of the theorem over the disjoint union of its carriers.
        lines.append("-- Uninterpreted sorts %s are the one type _U; functions and predicates take argument lists."
                     % ", ".join(json.dumps(sort, ensure_ascii=True) for sort in graph.sorts))
    elif graph.uninterpreted:
        lines.append("-- No uninterpreted sort: the type _U carries only the Boolean arguments of the predicates.")
    if any(decl.kind == z3.Z3_OP_UNINTERPRETED and "Bool" in decl.domain for decl in graph.declarations):
        lines.append("-- Boolean arguments of functions and predicates are injected into _U by _bool.")
    # Formulas over wide n-ary connectives render as right-nested And/Or chains
    # and long refutations nest hundreds of let-bound steps; every declaration
    # (definitions, lemmas, proof steps, the theorem) elaborates under a raised
    # recursion limit, scoped to this namespace. This is not a trust setting.
    lines.extend(["namespace " + namespace, "", "set_option maxRecDepth 100000", ""])
    signature = "(_atoms : Nat -> Prop)" + _valuation_binder(graph)
    classical = set()  # Term nodes containing an ite or abs: their classical instance is noncomputable.
    for node in range(len(graph.nodes)):
        if graph.is_term(node):
            if graph.kind(node) in (z3.Z3_OP_ITE, z3.Z3_OP_ABS) or any(arg in classical for arg in graph.arguments(node)):
                classical.add(node)
            lines.append("%sdef term_%d %s : %s := %s" % (
                "noncomputable " if node in classical else "", node, signature,
                graph.number_type if graph.is_arith(node) else "_U", _term_body(graph, node, variable_indices)))
        elif graph.decl(node).range == "Bool":
            lines.append("def formula_%d %s : Prop := %s" % (
                node, signature, _formula_body(graph, node, atom_indices)))
    rewrites, def_axioms, th_lemmas, decidable_atoms, decidable_formulas = {}, {}, {}, set(), set()
    for node in range(len(graph.nodes)):
        if graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA:
            _check_th_lemma(graph, node)
            lemma, term = _grind_lemma(graph, node, "th_lemma", atom_indices, variable_indices)
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
            term = (_select(position, len(graph.assertions), "_inputs") if outline else "_h%d" % position)
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
            term = _and_elim(graph, terms, node)
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
        outlined, witnesses = _outline_steps(graph, step_blocks, dependencies, signature)
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
        inputs = _fold("And.intro", ["_h%d" % i for i in range(len(graph.assertions))], "True.intro")
        lines.append("  proof_step_%d _atoms%s %s%s" % (
            graph.proof, graph.valuation, inputs, "".join(" " + name for name in witnesses)))
    else:
        for atom in sorted(decidable_atoms):
            lines.append("  refute_with_decidable (_atoms %d) fun _d%d =>" % (atom, atom))
        for formula in sorted(decidable_formulas):
            lines.append("  refute_with_decidable %s fun _df%d =>" % (_formula(graph, formula), formula))
        lines.extend(steps)
        lines.append("  _step_%d" % graph.proof)
    lines.extend(["", "end " + namespace, ""])
    return "\n".join(lines)


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
