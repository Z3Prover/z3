############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Reconstruct a supported native Boolean refutation in Lean.
############################################
"""Check asserted/unit-resolution certificates in Lean before publishing a proof."""

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
    elif kind == z3.Z3_OP_PR_ASSERTED:
        if name != "asserted" or domain != ("Bool",):
            raise ReconstructionError("invalid asserted declaration")
    elif kind == z3.Z3_OP_PR_UNIT_RESOLUTION:
        if (name != "unit-resolution" or len(domain) < 2 or domain[-1] != "Bool"
                or any(sort != "Proof" for sort in domain[:-1])):
            raise ReconstructionError("invalid unit-resolution declaration")
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
    lines.extend(["", "theorem unsat (_atoms : Nat -> Prop)"])
    assumptions = {}
    for position, assertion in enumerate(graph.assertions):
        lines.append("    (_h%d : %s)" % (position, _formula(assertion)))
        assumptions.setdefault(terms[assertion], position)
    lines.append("    : False :=")
    for node in range(len(graph.nodes)):
        if graph.decl(node).range != "Proof":
            continue
        conclusion = graph.conclusion(node)
        if graph.kind(node) == z3.Z3_OP_PR_ASSERTED:
            if terms[conclusion] not in assumptions:
                raise ReconstructionError("asserted node %d is not an original assertion" % node)
            term = "_h%d" % assumptions[terms[conclusion]]
        else:
            term = _resolution(graph, terms, node)
        lines.append("  let _step_%d : %s := %s" % (node, _formula(conclusion), term))
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
