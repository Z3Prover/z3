############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Reconstruct a supported native Boolean refutation in Lean.
############################################
"""Check native Boolean refutations using explicit Lean proof terms."""

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import z3

from proof_certificate import ProofExportError, parse_propositional_assertions


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
_FIXED_PROOF_RULES = {
    z3.Z3_OP_PR_ASSERTED: ("asserted", 0),
    z3.Z3_OP_PR_MODUS_PONENS: ("mp", 2),
    z3.Z3_OP_PR_REWRITE: ("rewrite", 0),
    z3.Z3_OP_PR_REFLEXIVITY: ("refl", 0),
    z3.Z3_OP_PR_SYMMETRY: ("symm", 1),
    z3.Z3_OP_PR_TRANSITIVITY: ("trans", 2),
    z3.Z3_OP_PR_AND_ELIM: ("and-elim", 1),
    z3.Z3_OP_PR_NOT_OR_ELIM: ("not-or-elim", 1),
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


def _declaration(raw):
    _fields(raw, ("kind", "name", "domain", "range", "parameters"), "declaration")
    kind, name = raw["kind"], raw["name"]
    domain = tuple(_list(raw["domain"], "declaration domain"))
    if (type(kind) is not int or type(name) is not str
            or raw["range"] not in ("Bool", "Proof")
            or any(sort not in ("Bool", "Proof") for sort in domain)
            or raw["parameters"] != []):
        raise ReconstructionError("invalid or parameterized native declaration")
    if raw["range"] == "Bool":
        if kind != z3.Z3_OP_UNINTERPRETED and _BOOL_NAMES.get(kind) != name:
            raise ReconstructionError("unsupported Boolean declaration: %s" % name)
        if any(sort != "Bool" for sort in domain):
            raise ReconstructionError("Boolean declarations cannot take proof arguments")
        expected = _FIXED_ARITY.get(kind)
        if kind in (z3.Z3_OP_AND, z3.Z3_OP_OR):
            expected = 2  # Native associative declarations have a binary domain.
        if expected is not None and len(domain) != expected:
            raise ReconstructionError("invalid Boolean declaration arity: %s" % name)
    elif kind in _FIXED_PROOF_RULES:
        expected_name, premises = _FIXED_PROOF_RULES[kind]
        if name != expected_name or domain != ("Proof",) * premises + ("Bool",):
            raise ReconstructionError("invalid %s declaration" % expected_name)
    elif kind in (z3.Z3_OP_PR_UNIT_RESOLUTION, z3.Z3_OP_PR_MONOTONICITY):
        expected_name = "unit-resolution" if kind == z3.Z3_OP_PR_UNIT_RESOLUTION else "monotonicity"
        minimum = 2 if kind == z3.Z3_OP_PR_UNIT_RESOLUTION else 1
        if (name != expected_name or len(domain) < minimum or domain[-1] != "Bool"
                or any(sort != "Proof" for sort in domain[:-1])):
            raise ReconstructionError("invalid %s declaration" % expected_name)
    else:
        raise ReconstructionError("unsupported native proof rule: %s" % name)
    return _Declaration(kind, name, domain, raw["range"])


def _validate_graph(source, certificate):
    _fields(certificate, (
        "format", "format_version", "z3_version", "fragment", "result",
        "verification", "source_smt2", "declarations", "nodes", "assertions",
        "proof", "rule_counts",
    ), "certificate")
    if (certificate["format"] != "z3-native-proof-dag"
            or type(certificate["format_version"]) is not int
            or certificate["format_version"] != 1
            or certificate["fragment"] != "propositional"
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
    graph = _Graph(declarations, tuple(nodes), assertions, root)
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


def _bind_input(source, graph):
    """Compare exact structures using hash-consing, not a digest or solver check."""
    context = z3.Context(proof=False)
    original = parse_propositional_assertions(source, context)
    interned, terms, atoms = {}, {}, {}

    def intern(kind, name, children):
        key = (kind, name, tuple(children))
        return interned.setdefault(key, len(interned))

    for index, node in enumerate(graph.nodes):
        decl = graph.decl(index)
        if decl.range != "Bool":
            continue
        name = ""
        if decl.kind == z3.Z3_OP_UNINTERPRETED:
            name = decl.name
            if name in atoms and atoms[name] != node.declaration:
                raise ReconstructionError("ambiguous Boolean symbol identity: %s" % name)
            atoms[name] = node.declaration
        terms[index] = intern(decl.kind, name, (terms[arg] for arg in node.arguments))

    original_terms, original_atoms = {}, set()
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
            original_atoms.add(name)
        original_terms[expr.get_id()] = intern(
            decl.kind(), name, (original_terms[child.get_id()] for child in expr.children()))
    if (set(atoms) != original_atoms
            or [terms[arg] for arg in graph.assertions]
            != [original_terms[expr.get_id()] for expr in original]):
        raise ReconstructionError("certificate assertions do not match the original input")
    return terms, atoms


def _fold(operator, arguments, identity):
    if not arguments:
        return identity
    result = arguments[-1]
    for argument in reversed(arguments[:-1]):
        result = "(%s %s %s)" % (operator, argument, result)
    return result


def _formula(node):
    return "(formula_%d _atoms)" % node


def _formula_body(graph, node, atom_indices):
    kind = graph.kind(node)
    args = [_formula(arg) for arg in graph.arguments(node)]
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
        term = "(Iff.refl %s)" % _formula(left)
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
            arguments.append("(Iff.refl %s)" % _formula(first))
        elif (terms[first], terms[second]) in evidence:
            arguments.append("_step_%d" % evidence[terms[first], terms[second]])
        else:
            raise ReconstructionError("monotonicity is missing an argument equivalence at node %d" % node)
    if not left_args:
        return "(Iff.refl %s)" % _formula(left)
    return _congruence_term(graph.kind(left), arguments)


def _and_elim(graph, terms, node):
    premise, conclusion = graph.arguments(node)
    conjunction = graph.conclusion(premise)
    if graph.kind(conjunction) != z3.Z3_OP_AND:
        raise ReconstructionError("and-elim requires a conjunction at node %d" % node)
    arguments = graph.arguments(conjunction)
    term = "_step_%d" % premise
    for position, argument in enumerate(arguments):
        if terms[argument] == terms[conclusion]:
            return "(And.left %s)" % term if position < len(arguments) - 1 else term
        term = "(And.right %s)" % term
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
                _formula(conclusion), conclusion, contradiction)), conclusion
    raise ReconstructionError("not-or-elim conclusion does not complement a disjunct at node %d" % node)


def _rewrite_lemma(graph, node, atom_indices):
    """Generate a Lean lemma checking every truth assignment by kernel reduction."""
    conclusion = graph.conclusion(node)
    _equivalence(graph, conclusion, "rewrite")
    reachable, atoms, pending = set(), set(), [conclusion]
    while pending:
        formula = pending.pop()
        if formula in reachable:
            continue
        reachable.add(formula)
        if graph.kind(formula) == z3.Z3_OP_UNINTERPRETED:
            atoms.add(atom_indices[graph.nodes[formula].declaration])
        pending.extend(graph.arguments(formula))
    atoms = sorted(atoms)
    lines = ["", "private theorem rewrite_%d (_atoms : Nat -> Prop)" % node]
    for atom in atoms:
        lines.append("    [_d%d : Decidable (_atoms %d)]" % (atom, atom))
    lines.extend([
        "    : %s := by" % _formula(conclusion),
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
    term = "(@rewrite_%d _atoms%s)" % (node, "".join(" _d%d" % atom for atom in atoms))
    return lines, atoms, term


def _resolution(graph, terms, node):
    premises = graph.arguments(node)[:-1]
    first, units = premises[0], premises[1:]
    literals = graph.clause(graph.conclusion(first))
    conclusion = graph.clause(graph.conclusion(node))
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


def reconstruct(source, certificate):
    """Return Lean source; callers must check it before claiming verification."""
    graph = _validate_graph(source, certificate)
    terms, atoms = _bind_input(source, graph)
    atom_indices = {decl: index for index, decl in enumerate(sorted(atoms.values()))}
    digest = hashlib.sha256(source.encode("utf-8")).hexdigest()
    namespace = "Z3Proofs.NativeCertificate.p" + digest
    lines = ["import Init", "", "-- Original input SHA-256: " + digest]
    for name, decl in sorted(atoms.items(), key=lambda item: atom_indices[item[1]]):
        lines.append("-- Atom %d: %s" % (atom_indices[decl], json.dumps(name, ensure_ascii=True)))
    lines.extend(["namespace " + namespace, ""])
    for node in range(len(graph.nodes)):
        if graph.decl(node).range == "Bool":
            lines.append("def formula_%d (_atoms : Nat -> Prop) : Prop := %s" % (
                node, _formula_body(graph, node, atom_indices)))
    rewrites, decidable_atoms = {}, set()
    for node in range(len(graph.nodes)):
        if graph.kind(node) == z3.Z3_OP_PR_REWRITE:
            lemma, support, term = _rewrite_lemma(graph, node, atom_indices)
            lines.extend(lemma)
            decidable_atoms.update(support)
            rewrites[node] = term
    assumptions = {}
    for position, assertion in enumerate(graph.assertions):
        assumptions.setdefault(terms[assertion], position)
    steps, decidable_formulas = [], set()
    for node in range(len(graph.nodes)):
        if graph.decl(node).range != "Proof":
            continue
        conclusion = graph.conclusion(node)
        if graph.kind(node) == z3.Z3_OP_PR_ASSERTED:
            if terms[conclusion] not in assumptions:
                raise ReconstructionError("asserted node %d is not an original assertion" % node)
            term = "_h%d" % assumptions[terms[conclusion]]
        elif graph.kind(node) == z3.Z3_OP_PR_MODUS_PONENS:
            term = _modus_ponens(graph, terms, node)
        elif graph.kind(node) == z3.Z3_OP_PR_REWRITE:
            term = rewrites[node]
        elif graph.kind(node) in (z3.Z3_OP_PR_REFLEXIVITY, z3.Z3_OP_PR_SYMMETRY,
                                 z3.Z3_OP_PR_TRANSITIVITY):
            term = _equivalence_step(graph, terms, node)
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
        steps.append("  let _step_%d : %s := %s" % (node, _formula(conclusion), term))
    if decidable_atoms or decidable_formulas:
        # A continuation ending in False can eliminate the temporary decidability
        # assumptions constructively, preserving the original theorem statement.
        lines.extend([
            "",
            "private theorem refute_with_decidable (p : Prop)",
            "    (k : Decidable p -> False) : False :=",
            "  k (.isFalse (fun hp => k (.isTrue hp)))",
        ])
    lines.extend(["", "theorem unsat (_atoms : Nat -> Prop)"])
    for position, assertion in enumerate(graph.assertions):
        lines.append("    (_h%d : %s)" % (position, _formula(assertion)))
    lines.append("    : False :=")
    for atom in sorted(decidable_atoms):
        lines.append("  refute_with_decidable (_atoms %d) fun _d%d =>" % (atom, atom))
    for formula in sorted(decidable_formulas):
        lines.append("  refute_with_decidable %s fun _df%d =>" % (_formula(formula), formula))
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
