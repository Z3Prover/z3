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
    ProofExportError, is_uninterpreted_sort, linear_combination_refutes, numeral_value, parse_assertions,
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
# An ite is the one Real or uninterpreted-sort term with a Boolean argument;
# Lean's ite needs a decidability instance, which the classical one provides.
# Both slices already depend on the standard axioms, through Rat and grind.
_REAL_ITE_DOMAIN = ("Bool", "Real", "Real")
_REAL_DOMAIN_PREDICATES = _ARITH_PREDICATE_NAMES.keys() | {z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT}
_COEFFICIENT_HINTS = ("farkas", "bound", "implied-eq")
_HINTS = _COEFFICIENT_HINTS + ("euf", "tseitin", "smt", "cnf")
_FRAGMENTS = ("propositional", "qf_lra", "qf_uf")
# Refutations with more proof steps than this are split into separately
# checked lemmas, none nesting more than _OUTLINE_CHUNK_STEPS steps: one
# nested term elaborates superlinearly and exhausts the default heartbeat
# budget between 1,000 and 2,000 steps.
_OUTLINE_PROOF_STEPS = 500
_OUTLINE_CHUNK_STEPS = 500
_NORMALIZED_REWRITE_ATOMS = 16
_RESERVED_SORTS = ("Bool", "Real", "Proof")
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
_FIXED_PROOF_RULES = {
    z3.Z3_OP_PR_ASSERTED: ("asserted", 0),
    z3.Z3_OP_PR_TH_LEMMA: ("th-lemma", 0),
    z3.Z3_OP_PR_HYPOTHESIS: ("hypothesis", 0),
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
}
_VARIADIC_PROOF_RULES = {
    z3.Z3_OP_PR_UNIT_RESOLUTION: ("unit-resolution", 1),
    z3.Z3_OP_PR_MONOTONICITY: ("monotonicity", 0),
    z3.Z3_OP_PR_TRANSITIVITY_STAR: ("trans*", 0),
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

    @property
    def valuation(self):
        """Extra Lean arguments of every formula: the Rat valuation or the uninterpreted interpretation."""
        return " _vars" if self.arithmetic else _UF_ARGUMENTS if self.sorts else ""

    def is_real(self, node):
        return self.decl(node).range == "Real"

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
    if raw["range"] in sorts:
        # Constants, functions, and ite inhabit an uninterpreted sort: no definitions.
        # A function may take arguments of any uninterpreted sort or Bool, never Real.
        if kind == z3.Z3_OP_ITE:
            if name != "if" or domain != ("Bool", raw["range"], raw["range"]):
                raise ReconstructionError("invalid uninterpreted-sort ite declaration")
        elif kind != z3.Z3_OP_UNINTERPRETED or any(argument not in sorts + ("Bool",) for argument in domain):
            raise ReconstructionError("unsupported uninterpreted-sort declaration: %s" % name)
    elif raw["range"] == "Real":
        if kind == z3.Z3_OP_ITE:
            if name != "if" or domain != _REAL_ITE_DOMAIN:
                raise ReconstructionError("invalid arithmetic ite declaration")
            return _Declaration(kind, name, domain, raw["range"], parameters)
        if kind == z3.Z3_OP_ANUM:
            try:
                Fraction(name)
            except (ValueError, ZeroDivisionError):
                raise ReconstructionError("invalid numeral declaration: %s" % name)
        elif kind != z3.Z3_OP_UNINTERPRETED and _REAL_NAMES.get(kind) != name:
            raise ReconstructionError("unsupported arithmetic declaration: %s" % name)
        if any(sort != "Real" for sort in domain):
            raise ReconstructionError("arithmetic declarations take Real arguments")
        expected = _REAL_ARITY.get(kind, 2)  # Associative operators have a binary domain.
        if len(domain) != expected:
            raise ReconstructionError("invalid arithmetic declaration arity: %s" % name)
    elif raw["range"] == "Bool":
        if kind in _ARITH_PREDICATE_NAMES:
            if _ARITH_PREDICATE_NAMES[kind] != name or domain != ("Real", "Real"):
                raise ReconstructionError("invalid arithmetic predicate declaration: %s" % name)
        else:
            if kind != z3.Z3_OP_UNINTERPRETED and _BOOL_NAMES.get(kind) != name:
                raise ReconstructionError("unsupported Boolean declaration: %s" % name)
            if kind == z3.Z3_OP_UNINTERPRETED and domain:
                # A predicate ranges over the uninterpreted sorts and Bool; the
                # exporter admits it only when the input also uses a sort.
                if not sorts or any(argument not in sorts + ("Bool",) for argument in domain):
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
        "verification", "source_smt2", "declarations", "nodes", "assertions",
        "proof", "rule_counts",
    ), "certificate")
    if (certificate["format"] != "z3-native-proof-dag"
            or type(certificate["format_version"]) is not int
            or certificate["format_version"] != 1
            or certificate["fragment"] not in _FRAGMENTS
            or certificate["result"] != "unsat"
            or certificate["verification"] != "unverified"
            or type(certificate["z3_version"]) is not str
            or not certificate["z3_version"]):
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
        elif decl.range == "Real" and decl.kind in (z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_MUL):
            domain = ("Real",) * max(len(arguments), 1)
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
    arithmetic = any(decl.range == "Real" for decl in declarations)
    if arithmetic and certificate["fragment"] == "propositional":
        raise ReconstructionError("propositional certificates cannot contain arithmetic")
    if arithmetic and sorts:
        raise ReconstructionError("certificates cannot mix arithmetic with an uninterpreted sort")
    if bool(sorts) != (certificate["fragment"] == "qf_uf"):
        raise ReconstructionError("only qf_uf certificates declare an uninterpreted sort, and they must use it")
    graph = _Graph(declarations, tuple(nodes), assertions, root, arithmetic, sorts)
    if any(graph.decl(arg).range != "Bool" for arg in assertions):
        raise ReconstructionError("assertion roots must be Boolean expressions")
    if graph.decl(root).range != "Proof" or graph.kind(graph.conclusion(root)) != z3.Z3_OP_FALSE:
        raise ReconstructionError("the root must be a proof concluding false")
    reported = certificate["rule_counts"]
    if (type(reported) is not dict
            or any(type(count) is not int or count <= 0 for count in reported.values())
            or reported != dict(counts)):
        raise ReconstructionError("native rule counts do not match the proof graph")
    return graph


# Symbol tables of a certificate, by (range sort class, has arguments): Boolean
# atoms, Real variables, elements of the uninterpreted sorts, functions into
# them, and predicates over them. Each table maps a name to its declaration.
_SYMBOL_TABLES = {
    ("Bool", False): "atoms", ("Real", False): "variables", ("sort", False): "elements",
    ("sort", True): "functions", ("Bool", True): "predicates",
}


def _symbol_table(range_name, arity, sorts):
    return _SYMBOL_TABLES.get(("sort" if range_name in sorts else range_name, arity > 0))


def _sort_name(sort):
    """The certificate's name for a sort of the original input."""
    kind = sort.kind()
    return "Bool" if kind == z3.Z3_BOOL_SORT else "Real" if kind == z3.Z3_REAL_SORT else sort.name()


def _bind_input(source, graph, fragment=None):
    """Compare exact structures using hash-consing, not a digest or solver check.

    Symbols are bound by name, so each name must denote one symbol of the input
    (Z3 accepts overloading by sort; the frontend rejects it and this check is
    repeated here) and the certificate's declaration must carry that symbol's
    full signature. Interned terms also carry their sort, so terms of different
    sorts never compare equal even though Lean renders every sort as _U.
    """
    context = z3.Context(proof=False)
    original, original_fragment = parse_assertions(source, context)
    if fragment is None:
        fragment = "qf_lra" if graph.arithmetic else "qf_uf" if graph.sorts else "propositional"
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
                    {"atoms": "Boolean", "variables": "Real"}.get(table, table[:-1]), name))
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
    return " (_vars : Nat -> Rat)" if graph.arithmetic else _UF_BINDERS if graph.sorts else ""


def _infix(operator, arguments):
    result = arguments[0]
    for argument in arguments[1:]:
        result = "(%s %s %s)" % (result, operator, argument)
    return result


def _application_arguments(graph, arguments, term, formula):
    """Render the argument list of a function or predicate over the uninterpreted sorts.

    A Boolean argument is injected into the carrier by _bool; its formula is
    rendered as a Prop.
    """
    return "[%s]" % ", ".join(term(arg) if graph.is_term(arg) else "(_bool %s)" % formula(arg)
                              for arg in arguments)


def _term_body(graph, node, variable_indices, term=None, formula=None):
    """Render a Real or uninterpreted-sort node; term and formula render its children.

    variable_indices numbers the Real variables, the elements, and the
    functions, each from zero; the defaults render children by definition name.
    """
    term = (lambda child: _term(graph, child)) if term is None else term
    formula = (lambda child: _formula(graph, child)) if formula is None else formula
    kind = graph.kind(node)
    arguments = graph.arguments(node)
    if kind == z3.Z3_OP_UNINTERPRETED:
        index = variable_indices[graph.nodes[node].declaration]
        if graph.is_real(node):
            return "_vars %d" % index
        if not arguments:
            return "_elems %d" % index
        return "_funs %d %s" % (index, _application_arguments(graph, arguments, term, formula))
    if kind == z3.Z3_OP_ANUM:
        value = Fraction(graph.decl(node).name)
        if value.denominator == 1:
            return "((%d : Rat))" % value.numerator
        return "((%d : Rat) / (%d : Rat))" % (value.numerator, value.denominator)
    if kind == z3.Z3_OP_ITE:
        # The instance's proposition is inferred from the condition.
        return "(@ite %s %s (Classical.propDecidable _) %s %s)" % (
            "Rat" if graph.is_real(node) else "_U",
            formula(arguments[0]), term(arguments[1]), term(arguments[2]))
    args = [term(arg) for arg in arguments]
    if kind == z3.Z3_OP_UMINUS:
        return "(-%s)" % args[0]
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
        if kind in _ARITH_PREDICATE_NAMES and graph.is_real(arguments[0]):
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


def _modus_ponens(graph, terms, node):
    premise, implication, conclusion = graph.arguments(node)
    relation = graph.conclusion(implication)
    kind = graph.kind(relation)
    if kind not in (z3.Z3_OP_IMPLIES, z3.Z3_OP_EQ, z3.Z3_OP_IFF):
        raise ReconstructionError("mp requires an implication or Boolean equivalence at node %d" % node)
    antecedent, consequent = graph.arguments(relation)
    if (terms[graph.conclusion(premise)] != terms[antecedent]
            or terms[conclusion] != terms[consequent]):
        raise ReconstructionError("incorrect mp antecedent or conclusion at node %d" % node)
    if kind == z3.Z3_OP_IMPLIES:
        return "(_step_%d _step_%d)" % (implication, premise)
    return "(Iff.mp _step_%d _step_%d)" % (implication, premise)


def _equivalence(graph, formula, rule):
    if graph.kind(formula) not in (z3.Z3_OP_EQ, z3.Z3_OP_IFF):
        raise ReconstructionError("%s requires a Boolean equivalence at node %d" % (rule, formula))
    return graph.arguments(formula)


def _equivalence_step(graph, terms, node):
    rule = graph.decl(node).name
    left, right = _equivalence(graph, graph.conclusion(node), rule)
    premises = graph.arguments(node)[:-1]
    if graph.kind(node) == z3.Z3_OP_PR_REFLEXIVITY:
        valid = terms[left] == terms[right]
        term = "(Iff.refl %s)" % _formula(graph, left)
    elif graph.kind(node) == z3.Z3_OP_PR_SYMMETRY:
        first, second = _equivalence(graph, graph.conclusion(premises[0]), rule)
        valid = terms[left] == terms[second] and terms[right] == terms[first]
        term = "(Iff.symm _step_%d)" % premises[0]
    else:
        first, middle = _equivalence(graph, graph.conclusion(premises[0]), rule)
        other_middle, last = _equivalence(graph, graph.conclusion(premises[1]), rule)
        valid = (terms[left] == terms[first] and terms[middle] == terms[other_middle]
                 and terms[right] == terms[last])
        term = "(Iff.trans _step_%d _step_%d)" % tuple(premises)
    if not valid:
        raise ReconstructionError("incorrect %s premises or conclusion at node %d" % (rule, node))
    return term


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

    path = []
    current = target
    while current != start:
        current, premise, reverse = parents[current]
        term = "_step_%d" % premise
        path.append("(Iff.symm %s)" % term if reverse else term)
    if not path:
        return "(Iff.refl %s)" % _formula(graph, left)
    path.reverse()
    # Balance the composition to avoid deeply nested Lean terms on long paths.
    while len(path) > 1:
        path = ["(Iff.trans %s %s)" % (path[index], path[index + 1])
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


def _monotonicity(graph, terms, node):
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
        if terms[first] == terms[second]:
            arguments.append("(Iff.refl %s)" % _formula(graph, first))
        elif (terms[first], terms[second]) in evidence:
            arguments.append("_step_%d" % evidence[terms[first], terms[second]])
        else:
            raise ReconstructionError("monotonicity is missing an argument equivalence at node %d" % node)
    if not left_args:
        return "(Iff.refl %s)" % _formula(graph, left)
    return _congruence_term(graph.kind(left), arguments)


def _and_elim(graph, terms, node):
    premise, conclusion = graph.arguments(node)
    conjunction = graph.conclusion(premise)
    if graph.kind(conjunction) != z3.Z3_OP_AND:
        raise ReconstructionError("and-elim requires a conjunction at node %d" % node)
    arguments = graph.arguments(conjunction)
    for position, argument in enumerate(arguments):
        if terms[argument] == terms[conclusion]:
            return _project(position, len(arguments), "_step_%d" % premise)
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
        if (graph.is_real(formula) or not arguments or not graph.is_real(arguments[0])
                or (kind not in _ARITH_PREDICATE_NAMES and kind != z3.Z3_OP_EQ)):
            continue
        relation, terms, constant = _atom_constraint(graph, formula)
        scale = _common_denominator(terms, constant)
        if scale == 1:
            continue
        helpers.append("  have _s%d : %s -> (%s %s ((0 : Rat))) := by grind" % (
            formula, _inline(graph, formula, atom_indices, variable_indices),
            _scaled_form(graph, terms, constant, scale, atom_indices, variable_indices), relation))
    return helpers


def _common_denominator(terms, constant):
    scale = 1
    for value in list(terms.values()) + [constant]:
        scale = scale * value.denominator // _gcd(scale, value.denominator)
    return scale


def _scaled_form(graph, terms, constant, scale, atom_indices, variable_indices):
    """Render scale * (terms + constant) with integer coefficients, as grind's linear module wants it."""
    # The linear form's variables are Real variables and opaque ite terms.
    parts = ["((%d : Rat)) * %s" % (terms[variable] * scale, _inline(graph, variable, atom_indices, variable_indices))
             for variable in sorted(terms)]
    parts.append("((%d : Rat))" % (constant * scale))
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
        if not graph.is_real(node) or graph.kind(node) != z3.Z3_OP_ITE:
            continue
        condition, then_branch, else_branch = graph.arguments(node)

        def inline(sub):
            return "(%s)" % _inline(graph, sub, atom_indices, variable_indices)

        for side, branch, hypothesis, lemma in (
                (0, then_branch, inline(condition), "ite_eq_left"),
                (1, else_branch, "(Not %s)" % inline(condition), "ite_eq_right")):
            terms = {}
            constant = _linear_term(graph, branch, Fraction(1), terms)
            scale = _common_denominator(terms, constant)
            if scale == 1:
                helpers.append("  have _g%d_%d : %s -> %s = %s := fun _h => %s _h" % (
                    node, side, hypothesis, inline(node), inline(branch), lemma))
            else:
                helpers.append("  have _g%d_%d : %s -> ((%d : Rat)) * %s = (%s) := fun _h => by rw [%s _h]; grind" % (
                    node, side, hypothesis, scale, inline(node),
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
    the standard axioms, so arithmetic lemmas do too.
    """
    conclusion = graph.conclusion(node)
    reachable, _ = _reachable(graph, conclusion)
    definitions = ["%s_%d" % ("term" if graph.is_term(formula) else "formula", formula)
                   for formula in sorted(reachable, reverse=True)]
    lines = [
        "",
        "set_option maxHeartbeats 1000000 in",
        "private theorem %s_%d (_atoms : Nat -> Prop)%s" % (prefix, node, _valuation_binder(graph)),
        "    : %s := by" % _formula(graph, conclusion),
        "  unfold " + " ".join(definitions),
    ]
    if graph.arithmetic:
        lines.extend(_scaling_helpers(graph, reachable, atom_indices, variable_indices))
        lines.extend(_ite_gate_helpers(graph, reachable, atom_indices, variable_indices))
    if graph.sorts:
        lines.extend(_boolean_argument_helpers(graph, reachable, atom_indices, variable_indices))
    # Large Boolean/arithmetic rewrites can require more than grind's default
    # nine case splits, even though every arithmetic atom remains linear.
    lines.append("  grind (splits := 64)")
    return lines, "(%s_%d _atoms%s)" % (prefix, node, graph.valuation)


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


def _rewrite_lemma(graph, node, atom_indices, variable_indices=None):
    """Generate a Lean lemma checking every truth assignment by kernel reduction."""
    conclusion = graph.conclusion(node)
    _equivalence(graph, conclusion, "rewrite")
    reachable, theory = _reachable(graph, conclusion)
    if theory:
        atoms = [formula for formula in sorted(reachable)
                 if graph.kind(formula) in _ARITH_PREDICATE_NAMES.keys() | {z3.Z3_OP_EQ}
                 and graph.arguments(formula) and graph.is_real(graph.arguments(formula)[0])]
        distinct = any(graph.kind(formula) == z3.Z3_OP_DISTINCT for formula in reachable)
        if len(atoms) > _NORMALIZED_REWRITE_ATOMS and not distinct:
            lines, term = _normalized_rewrite(graph, node, reachable, atoms, atom_indices, variable_indices)
        else:
            lines, term = _grind_lemma(graph, node, "rewrite", atom_indices, variable_indices)
        return lines, set(), term
    atoms = sorted(atom_indices[graph.nodes[formula].declaration]
                   for formula in reachable if graph.kind(formula) == z3.Z3_OP_UNINTERPRETED)
    lines = ["", "private theorem rewrite_%d (_atoms : Nat -> Prop)%s" % (node, _valuation_binder(graph))]
    for atom in atoms:
        lines.append("    [_d%d : Decidable (_atoms %d)]" % (atom, atom))
    lines.extend([
        "    : %s := by" % _formula(graph, conclusion),
        "  unfold " + " ".join("formula_%d" % formula for formula in sorted(reachable, reverse=True)),
    ])
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


def _normalized_rewrite(graph, node, reachable, atoms, atom_indices, variable_indices):
    """Separate linear atom normalization from propositional rewrite search."""
    def numeral(value):
        return ("((%d : Rat))" % value.numerator if value.denominator == 1 else
                "((%d : Rat) / (%d : Rat))" % (value.numerator, value.denominator))

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
        if terms:
            first = min(terms, key=lambda var: variable_indices[graph.nodes[var].declaration])
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
        expression = "(%s %s ((0 : Rat)))" % (" + ".join(parts), relation)
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
                   if not graph.is_real(formula) and formula not in atoms]
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
    for c and rewrites the ite with ite_eq_left or ite_eq_right.
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
            if terms[branch] == terms[then_branch]:
                equation, guard_polarity = "(ite_eq_left _hc)", False
            elif terms[branch] == terms[else_branch]:
                equation, guard_polarity = "(ite_eq_right _hnc)", True
            else:
                continue
            if flipped:
                equation = "(Eq.symm %s)" % equation
            for guard_position, guard in enumerate(literals):
                if guard_polarity:
                    matches = terms[guard] == terms[condition]
                else:
                    matches = (graph.kind(guard) == z3.Z3_OP_NOT
                               and terms[graph.arguments(guard)[0]] == terms[condition])
                if not matches:
                    continue
                equation = _inject(position, len(literals), equation)
                if guard_polarity:
                    cases = (_inject(guard_position, len(literals), "_hc"), equation)
                else:
                    cases = (equation, _inject(guard_position, len(literals), "_hnc"))
                lines = [
                    "",
                    "private theorem def_axiom_%d (_atoms : Nat -> Prop)%s" % (node, _valuation_binder(graph)),
                    "    [_df%d : Decidable %s]" % (condition, _formula(graph, condition)),
                    "    : %s :=" % _formula(graph, conclusion),
                    "  @Decidable.byCases %s _ _df%d (fun _hc => %s) (fun _hnc => %s)" % (
                        _formula(graph, condition), condition, cases[0], cases[1]),
                ]
                term = "(@def_axiom_%d _atoms%s _df%d)" % (node, graph.valuation, condition)
                return lines, {condition}, term
    return None


def _def_axiom_lemma(graph, terms, node):
    """Prove a Boolean gate clause independently of all input assertions."""
    gate = _ite_gate_lemma(graph, terms, node)
    if gate is not None:
        return gate
    conclusion = graph.conclusion(node)
    literals = graph.clause(conclusion)
    facts, formulas, steps, support = {}, {}, [], {conclusion}
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
        key = terms[formula], truth
        facts.setdefault(key, evidence)
        formulas.setdefault(key, formula)

    def fact(formula, truth):
        negations = []
        while graph.kind(formula) == z3.Z3_OP_NOT:
            negations.append(truth)
            formula, truth = graph.arguments(formula)[0], not truth
        evidence = facts.get((terms[formula], truth))
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
    """Accumulate the linear form of a Real node into terms; return its constant part.

    Variables and Real ite terms are the atoms of the linear form; an ite is
    opaque to Farkas reasoning and tied to its branches by gate clauses.
    """
    kind = graph.kind(node)
    arguments = graph.arguments(node)
    if kind == z3.Z3_OP_ANUM:
        return scale * Fraction(graph.decl(node).name)
    if kind in (z3.Z3_OP_UNINTERPRETED, z3.Z3_OP_ITE):
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
    if (kind not in _ARITH_PREDICATE_NAMES and kind != z3.Z3_OP_EQ) or not graph.is_real(arguments[0]):
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
    return relation, {k: v for k, v in terms.items() if v != 0}, constant


def _check_th_lemma(graph, node):
    """Check Farkas combinations and implied-equality shapes before calling Lean."""
    parameters = graph.decl(node).parameters
    if parameters[0] not in _COEFFICIENT_HINTS:
        return
    literals = graph.clause(graph.conclusion(node))
    coefficients = [Fraction(parameter) for parameter in parameters[1:]]
    if len(coefficients) != len(literals):
        raise ReconstructionError("th-lemma %s has %d coefficients for %d literals at node %d" % (
            parameters[0], len(coefficients), len(literals), node))
    if parameters[0] == "implied-eq":
        if not literals:
            raise ReconstructionError("implied-eq th-lemma must end in a Real equality")
        equality, polarity = literals[-1], True
        while graph.kind(equality) == z3.Z3_OP_NOT:
            equality, polarity = graph.arguments(equality)[0], not polarity
        if (not polarity or graph.kind(equality) != z3.Z3_OP_EQ
                or not graph.is_real(graph.arguments(equality)[0])):
            raise ReconstructionError("implied-eq th-lemma must end in a Real equality")
        _atom_constraint(graph, equality)
        literals, coefficients = literals[:-1], coefficients[:-1]
    constraints = []
    for coefficient, literal in zip(coefficients, literals):
        relation, terms, constant = _linear_constraint(graph, literal)
        constraints.append((coefficient, relation, terms, constant))
    if parameters[0] != "implied-eq" and not linear_combination_refutes(constraints):
        raise ReconstructionError("th-lemma %s coefficients do not refute its literals at node %d" % (
            parameters[0], node))


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
    if len(literals) == 1:
        return branch(0, "_step_%d" % first)
    result = branch(len(literals) - 1, "_tail")
    for position in reversed(range(len(literals) - 1)):
        subject = "_step_%d" % first if position == 0 else "_tail"
        result = "(Or.elim %s (fun _literal => %s) (fun _tail => %s))" % (
            subject, branch(position, "_literal"), result)
    return result


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
    classical = bool(graph.arithmetic or graph.sorts)
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
            "", "set_option maxRecDepth 100000 in",
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
    terms, tables = _bind_input(source, graph, certificate["fragment"])
    # Each symbol table is numbered from zero; a declaration belongs to one table,
    # so the Boolean-valued and term-valued tables can share one index map each.
    indices = {table: {decl: index for index, decl in enumerate(sorted(symbols.values()))}
               for table, symbols in tables.items()}
    atom_indices = {**indices["atoms"], **indices["predicates"]}
    variable_indices = {**indices["variables"], **indices["elements"], **indices["functions"]}
    digest = hashlib.sha256(source.encode("utf-8")).hexdigest()
    namespace = "Z3Proofs.NativeCertificate.p" + digest
    lines = ["import Init", "", "-- Original input SHA-256: " + digest]
    for table, label in (("atoms", "Atom"), ("variables", "Variable"), ("elements", "Element"),
                         ("functions", "Function"), ("predicates", "Predicate")):
        for name, decl in sorted(tables[table].items(), key=lambda item: indices[table][item[1]]):
            lines.append("-- %s %d: %s" % (label, indices[table][decl], json.dumps(name, ensure_ascii=True)))
    if graph.arithmetic:
        lines.append("-- Real variables are encoded as Rat; see the exporter documentation.")
    if len(graph.sorts) == 1:
        lines.append("-- Uninterpreted sort %s is the type _U; functions and predicates take argument lists."
                     % json.dumps(graph.sorts[0], ensure_ascii=True))
    elif graph.sorts:
        # One carrier for every sort is sound: a many-sorted model is an instance
        # of the theorem over the disjoint union of its carriers.
        lines.append("-- Uninterpreted sorts %s are the one type _U; functions and predicates take argument lists."
                     % ", ".join(json.dumps(sort, ensure_ascii=True) for sort in graph.sorts))
    if any(decl.kind == z3.Z3_OP_UNINTERPRETED and "Bool" in decl.domain for decl in graph.declarations):
        lines.append("-- Boolean arguments of functions and predicates are injected into _U by _bool.")
    lines.extend(["namespace " + namespace, ""])
    signature = "(_atoms : Nat -> Prop)" + _valuation_binder(graph)
    classical = set()  # Real nodes containing an ite: their classical instance is noncomputable.
    for node in range(len(graph.nodes)):
        if graph.is_term(node):
            if graph.kind(node) == z3.Z3_OP_ITE or any(arg in classical for arg in graph.arguments(node)):
                classical.add(node)
            lines.append("%sdef term_%d %s : %s := %s" % (
                "noncomputable " if node in classical else "", node, signature,
                "Rat" if graph.is_real(node) else "_U", _term_body(graph, node, variable_indices)))
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
            lemma, support, term = _rewrite_lemma(graph, node, atom_indices, variable_indices)
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
            term = (_project(position, len(graph.assertions), "_inputs") if outline else "_h%d" % position)
        elif graph.kind(node) == z3.Z3_OP_PR_HYPOTHESIS:
            hypothesis = hypothesis_formulas.setdefault(terms[conclusion], conclusion)
            dependencies[node] = (hypothesis,)
            term = "_hyp%d" % hypothesis
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
            term = _monotonicity(graph, terms, node)
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
    # Long refutations nest hundreds of let-bound steps; raise the elaborator's
    # recursion limit so they elaborate. This is not a trust setting.
    lines.extend(["", "set_option maxRecDepth 100000 in", "theorem unsat " + signature])
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
