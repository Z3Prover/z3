############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Reconstruct a supported native Boolean or QF_LRA refutation in Lean.
############################################
"""Check native Boolean and linear real arithmetic refutations in Lean.

Boolean steps become explicit Lean proof terms. Arithmetic atoms are encoded
over Rat, and theory lemmas and arithmetic rewrites are discharged by Lean's
grind tactic after a Python pre-check of the recorded Farkas combination.
"""

import argparse
from collections import Counter, deque
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import z3

from proof_certificate import (
    ProofExportError, linear_combination_refutes, numeral_value, parse_assertions,
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
_REAL_DOMAIN_PREDICATES = _ARITH_PREDICATE_NAMES.keys() | {z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT}
_COEFFICIENT_HINTS = ("farkas", "bound", "implied-eq")
_HINTS = _COEFFICIENT_HINTS + ("euf", "tseitin", "smt", "cnf")
_FRAGMENTS = ("propositional", "qf_lra")
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

    @property
    def valuation(self):
        """Extra Lean arguments of every formula: the Rat valuation when arithmetic is present."""
        return " _vars" if self.arithmetic else ""

    def is_real(self, node):
        return self.decl(node).range == "Real"

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


def _declaration(raw):
    _fields(raw, ("kind", "name", "domain", "range", "parameters"), "declaration")
    kind, name = raw["kind"], raw["name"]
    domain = tuple(_list(raw["domain"], "declaration domain"))
    if (type(kind) is not int or type(name) is not str
            or raw["range"] not in ("Bool", "Real", "Proof")
            or any(sort not in ("Bool", "Real", "Proof") for sort in domain)):
        raise ReconstructionError("invalid native declaration")
    parameters = _parameters(kind, name, raw["parameters"])
    if raw["range"] == "Real":
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
            real_domain = kind in (z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT) and bool(domain) and domain[0] == "Real"
            if any(sort != ("Real" if real_domain else "Bool") for sort in domain):
                raise ReconstructionError("Boolean declarations cannot mix argument sorts")
            expected = _FIXED_ARITY.get(kind)
            if kind in (z3.Z3_OP_AND, z3.Z3_OP_OR):
                expected = 2  # Native associative declarations have a binary domain.
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
    declarations = tuple(_declaration(raw) for raw in _list(certificate["declarations"], "declarations"))
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
        elif decl.range == "Bool" and decl.kind == z3.Z3_OP_DISTINCT and decl.domain[:1] == ("Real",):
            domain = ("Real",) * len(arguments)
        if len(arguments) != len(domain):
            raise ReconstructionError("wrong number of arguments at node %d" % index)
        for argument, sort in zip(arguments, domain):
            if declarations[nodes[argument].declaration].range != sort:
                raise ReconstructionError("wrong argument sort at node %d" % index)
        nodes.append(_Node(declaration, arguments))
        if decl.range == "Proof":
            counts[decl.name] += 1
    assertions = tuple(_index(arg, len(nodes), "assertion")
                       for arg in _list(certificate["assertions"], "assertions"))
    root = _index(certificate["proof"], len(nodes), "proof")
    arithmetic = any(decl.range == "Real" for decl in declarations)
    if arithmetic and certificate["fragment"] == "propositional":
        raise ReconstructionError("propositional certificates cannot contain arithmetic")
    graph = _Graph(declarations, tuple(nodes), assertions, root, arithmetic)
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


def _bind_input(source, graph, fragment=None):
    """Compare exact structures using hash-consing, not a digest or solver check."""
    context = z3.Context(proof=False)
    original, original_fragment = parse_assertions(source, context)
    if fragment is None:
        fragment = "qf_lra" if graph.arithmetic else "propositional"
    if original_fragment != fragment:
        raise ReconstructionError("the input is in fragment %s, not %s" % (original_fragment, fragment))
    interned, terms, atoms, variables = {}, {}, {}, {}

    def intern(kind, name, children):
        key = (kind, name, tuple(children))
        return interned.setdefault(key, len(interned))

    for index, node in enumerate(graph.nodes):
        decl = graph.decl(index)
        if decl.range == "Proof":
            continue
        name = ""
        if decl.kind == z3.Z3_OP_UNINTERPRETED:
            name = decl.name
            symbols = variables if decl.range == "Real" else atoms
            if name in symbols and symbols[name] != node.declaration:
                raise ReconstructionError("ambiguous %s symbol identity: %s" % (
                    "Real" if decl.range == "Real" else "Boolean", name))
            if name in (variables if decl.range == "Bool" else atoms):
                raise ReconstructionError("symbol used with two sorts: %s" % name)
            symbols[name] = node.declaration
        elif decl.kind == z3.Z3_OP_ANUM:
            name = str(Fraction(decl.name))
        terms[index] = intern(decl.kind, name, (terms[arg] for arg in node.arguments))

    original_terms, original_atoms, original_variables = {}, set(), set()
    pending = [(expr, False) for expr in reversed(list(original))]
    while pending:
        expr, expanded = pending.pop()
        if expr.get_id() in original_terms:
            continue
        if not expanded:
            pending.append((expr, True))
            pending.extend((child, False) for child in reversed(expr.children()))
            continue
        decl, name = expr.decl(), ""
        if decl.kind() == z3.Z3_OP_UNINTERPRETED:
            name = str(decl.name())
            (original_variables if z3.is_real(expr) else original_atoms).add(name)
        elif decl.kind() == z3.Z3_OP_ANUM:
            name = str(numeral_value(expr))
        original_terms[expr.get_id()] = intern(
            decl.kind(), name, (original_terms[child.get_id()] for child in expr.children()))
    if (set(atoms) != original_atoms or set(variables) != original_variables
            or [terms[arg] for arg in graph.assertions]
            != [original_terms[expr.get_id()] for expr in original]):
        raise ReconstructionError("certificate assertions do not match the original input")
    return terms, atoms, variables


def _fold(operator, arguments, identity):
    if not arguments:
        return identity
    result = arguments[-1]
    for argument in reversed(arguments[:-1]):
        result = "(%s %s %s)" % (operator, argument, result)
    return result


def _formula(graph, node):
    return "(formula_%d _atoms%s)" % (node, graph.valuation)


def _term(node):
    return "(term_%d _vars)" % node


def _valuation_binder(graph):
    return " (_vars : Nat -> Rat)" if graph.arithmetic else ""


def _infix(operator, arguments):
    result = arguments[0]
    for argument in arguments[1:]:
        result = "(%s %s %s)" % (result, operator, argument)
    return result


def _term_body(graph, node, variable_indices):
    kind = graph.kind(node)
    args = [_term(arg) for arg in graph.arguments(node)]
    if kind == z3.Z3_OP_UNINTERPRETED:
        return "_vars %d" % variable_indices[graph.nodes[node].declaration]
    if kind == z3.Z3_OP_ANUM:
        value = Fraction(graph.decl(node).name)
        if value.denominator == 1:
            return "((%d : Rat))" % value.numerator
        return "((%d : Rat) / (%d : Rat))" % (value.numerator, value.denominator)
    if kind == z3.Z3_OP_UMINUS:
        return "(-%s)" % args[0]
    return _infix(_REAL_NAMES[kind], args)


def _formula_body(graph, node, atom_indices):
    kind = graph.kind(node)
    arguments = graph.arguments(node)
    if arguments and graph.is_real(arguments[0]):
        args = [_term(arg) for arg in arguments]
        if kind in _ARITH_PREDICATE_NAMES:
            return "(%s %s %s)" % (args[0], _ARITH_PREDICATE_NAMES[kind], args[1])
        if kind == z3.Z3_OP_EQ:
            return "(%s = %s)" % tuple(args)
        if kind == z3.Z3_OP_DISTINCT:
            pairs = ["(Not (%s = %s))" % (left, right)
                     for index, left in enumerate(args) for right in args[index + 1:]]
            return _fold("And", pairs, "True")
        raise ReconstructionError("unsupported arithmetic atom")
    args = [_formula(graph, arg) for arg in arguments]
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
    """Return the formula and term nodes reachable from a conclusion, and whether any is arithmetic."""
    reachable, pending, arithmetic = set(), [conclusion], False
    while pending:
        formula = pending.pop()
        if formula in reachable:
            continue
        reachable.add(formula)
        arithmetic = arithmetic or graph.is_real(formula)
        pending.extend(graph.arguments(formula))
    return reachable, arithmetic


def _inline(graph, node, atom_indices, variable_indices):
    """Render a formula or term with every definition expanded, as unfold would."""
    kind = graph.kind(node)
    arguments = graph.arguments(node)
    if graph.is_real(node):
        if kind == z3.Z3_OP_UNINTERPRETED:
            return "_vars %d" % variable_indices[graph.nodes[node].declaration]
        if kind == z3.Z3_OP_ANUM:
            return _term_body(graph, node, variable_indices)
        args = [_inline(graph, arg, atom_indices, variable_indices) for arg in arguments]
        if kind == z3.Z3_OP_UMINUS:
            return "(-%s)" % args[0]
        return _infix(_REAL_NAMES[kind], args)
    if arguments and graph.is_real(arguments[0]):
        args = [_inline(graph, arg, atom_indices, variable_indices) for arg in arguments]
        if kind in _ARITH_PREDICATE_NAMES:
            return "(%s %s %s)" % (args[0], _ARITH_PREDICATE_NAMES[kind], args[1])
        if kind == z3.Z3_OP_EQ:
            return "(%s = %s)" % tuple(args)
    raise ReconstructionError("only arithmetic atoms are rendered inline")


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
        scale = 1
        for value in list(terms.values()) + [constant]:
            scale = scale * value.denominator // _gcd(scale, value.denominator)
        if scale == 1:
            continue
        parts = ["((%d : Rat)) * _vars %d" % (terms[variable] * scale, variable_indices[graph.nodes[variable].declaration])
                 for variable in sorted(terms, key=lambda v: variable_indices[graph.nodes[v].declaration])]
        parts.append("((%d : Rat))" % (constant * scale))
        helpers.append("  have _s%d : %s -> (%s %s ((0 : Rat))) := by grind" % (
            formula, _inline(graph, formula, atom_indices, variable_indices), " + ".join(parts), relation))
    return helpers


def _gcd(left, right):
    while right:
        left, right = right, left % right
    return left


def _grind_lemma(graph, node, prefix, atom_indices, variable_indices):
    """Prove a conclusion over arithmetic atoms with grind after unfolding its definitions.

    grind decides linear arithmetic over ordered fields and propositional
    structure; the Lean kernel checks the proof it produces. Lean core's Rat
    library already depends on the standard axioms, so these lemmas do too.
    """
    conclusion = graph.conclusion(node)
    reachable, _ = _reachable(graph, conclusion)
    definitions = ["%s_%d" % ("term" if graph.is_real(formula) else "formula", formula)
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
    lines.append("  grind")
    return lines, "(%s_%d _atoms%s)" % (prefix, node, graph.valuation)


def _rewrite_lemma(graph, node, atom_indices, variable_indices=None):
    """Generate a Lean lemma checking every truth assignment by kernel reduction."""
    conclusion = graph.conclusion(node)
    _equivalence(graph, conclusion, "rewrite")
    reachable, arithmetic = _reachable(graph, conclusion)
    if arithmetic:
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
    return None


def _def_axiom_lemma(graph, terms, node):
    """Prove a Boolean gate clause independently of all input assertions."""
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
    """Accumulate the linear form of a Real node into terms; return its constant part."""
    kind = graph.kind(node)
    arguments = graph.arguments(node)
    if kind == z3.Z3_OP_ANUM:
        return scale * Fraction(graph.decl(node).name)
    if kind == z3.Z3_OP_UNINTERPRETED:
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
        constants, variable = [], None
        for arg in arguments:
            factor = _linear_term(graph, arg, Fraction(1), {})
            if _reachable(graph, arg)[1] and any(graph.kind(f) == z3.Z3_OP_UNINTERPRETED
                                                  for f in _reachable(graph, arg)[0]):
                if variable is not None:
                    raise ReconstructionError("nonlinear multiplication in a theory lemma")
                variable = arg
            else:
                constants.append(factor)
        for constant in constants:
            scale *= constant
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


def reconstruct(source, certificate):
    """Return Lean source; callers must check it before claiming verification."""
    graph = _validate_graph(source, certificate)
    terms, atoms, variables = _bind_input(source, graph, certificate["fragment"])
    atom_indices = {decl: index for index, decl in enumerate(sorted(atoms.values()))}
    variable_indices = {decl: index for index, decl in enumerate(sorted(variables.values()))}
    digest = hashlib.sha256(source.encode("utf-8")).hexdigest()
    namespace = "Z3Proofs.NativeCertificate.p" + digest
    lines = ["import Init", "", "-- Original input SHA-256: " + digest]
    for name, decl in sorted(atoms.items(), key=lambda item: atom_indices[item[1]]):
        lines.append("-- Atom %d: %s" % (atom_indices[decl], json.dumps(name, ensure_ascii=True)))
    for name, decl in sorted(variables.items(), key=lambda item: variable_indices[item[1]]):
        lines.append("-- Variable %d: %s" % (variable_indices[decl], json.dumps(name, ensure_ascii=True)))
    if graph.arithmetic:
        lines.append("-- Real variables are encoded as Rat; see the exporter documentation.")
    lines.extend(["namespace " + namespace, ""])
    signature = "(_atoms : Nat -> Prop)" + (" (_vars : Nat -> Rat)" if graph.arithmetic else "")
    for node in range(len(graph.nodes)):
        if graph.is_real(node):
            lines.append("def term_%d (_vars : Nat -> Rat) : Rat := %s" % (
                node, _term_body(graph, node, variable_indices)))
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
    steps = []
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
            term = "_h%d" % assumptions[terms[conclusion]]
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
        steps.append("  let _step_%d%s : %s :=" % (node, parameters, _formula(graph, conclusion)))
        if graph.kind(node) != z3.Z3_OP_PR_LEMMA:
            for premise in dict.fromkeys(premises):
                if dependencies[premise]:
                    arguments = "".join(" _hyp%d" % hypothesis for hypothesis in dependencies[premise])
                    steps.append("    let _step_%d := _step_%d%s" % (premise, premise, arguments))
        steps.append("    " + term)
    if dependencies[graph.proof]:
        raise ReconstructionError("the root proof has undischarged hypotheses")
    if decidable_atoms or decidable_formulas:
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
    for atom in sorted(decidable_atoms):
        lines.append("  refute_with_decidable (_atoms %d) fun _d%d =>" % (atom, atom))
    for formula in sorted(decidable_formulas):
        lines.append("  refute_with_decidable %s fun _df%d =>" % (_formula(graph, formula), formula))
    lines.extend(steps)
    lines.extend(["  _step_%d" % graph.proof, "", "end " + namespace, ""])
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
