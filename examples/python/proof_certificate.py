############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Export native Boolean and linear real arithmetic refutations for
# independent proof consumers.
############################################
"""Export an unverified native proof DAG for one propositional or QF_LRA SMT-LIB problem."""

import argparse
from collections import Counter
from fractions import Fraction
import json
import os
import re
import subprocess
import sys
import tempfile

import z3


class ProofExportError(Exception):
    """The input or native proof is outside the exporter's supported fragment."""


_TOKEN = re.compile(
    r'\s+|;[^\r\n]*|"(?:[^"]|"")*"|\|[^|\\]*\||[()]|[^\s();"|#]+|#[xb][0-9a-fA-F]+',
    re.DOTALL,
)
_ASSERTION_COMMANDS = {
    "set-logic", "set-info", "declare-const", "declare-fun", "define-fun", "assert",
}
_BOOLEAN_OPERATORS = {
    z3.Z3_OP_TRUE, z3.Z3_OP_FALSE, z3.Z3_OP_NOT, z3.Z3_OP_AND, z3.Z3_OP_OR,
    z3.Z3_OP_IMPLIES, z3.Z3_OP_XOR, z3.Z3_OP_IFF, z3.Z3_OP_EQ,
    z3.Z3_OP_DISTINCT, z3.Z3_OP_ITE,
}
# Linear real arithmetic: atoms over Real terms built from variables, numerals,
# sums, differences, negation, scaling by a numeral, and division by a numeral.
_ARITH_PREDICATES = {z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT}
_ARITH_OPERATORS = {z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS, z3.Z3_OP_MUL, z3.Z3_OP_DIV}
_ARITH_NAMES = {
    z3.Z3_OP_LE: "<=", z3.Z3_OP_GE: ">=", z3.Z3_OP_LT: "<", z3.Z3_OP_GT: ">",
    z3.Z3_OP_ADD: "+", z3.Z3_OP_SUB: "-", z3.Z3_OP_UMINUS: "-", z3.Z3_OP_MUL: "*",
    z3.Z3_OP_DIV: "/",
}
# Clause-log hint encodings; replay handles each hint's clause convention.
_COEFFICIENT_HINTS = ("farkas", "bound", "implied-eq")
_LITERAL_HINTS = ("euf", "tseitin", "smt", "alldiff")
# Synthesized by the exporter, not logged by Z3: an original assertion implies
# one of the clauses it was split into.
_CNF_HINT = "cnf"
# The clause log starts after preprocessing, so every pass that rewrites one
# assertion using another is disabled. bound_simplifier runs solve_eqs and
# propagate_values internally regardless of their own options.
_NO_PREPROCESSING = (
    "(set-option :smt.solve_eqs false)\n(set-option :smt.propagate_values false)\n"
    "(set-option :smt.elim_unconstrained false)\n(set-option :smt.bound_simplifier false)\n"
)


def _commands(source):
    position, depth, start = 0, 0, 0
    tokens = []
    while position < len(source):
        match = _TOKEN.match(source, position)
        if match is None:
            raise ProofExportError("unsupported or unterminated token at character %d" % position)
        position = match.end()
        token = match.group()
        if token.isspace() or token.startswith(";"):
            continue
        if depth == 0:
            if token != "(":
                raise ProofExportError("expected a top-level SMT-LIB command")
            start, tokens = match.start(), []
        tokens.append(token)
        if token == "(":
            depth += 1
        elif token == ")":
            depth -= 1
        if depth == 0:
            if len(tokens) < 3:
                raise ProofExportError("expected an SMT-LIB command name")
            yield tokens, source[start:position]
    if depth:
        raise ProofExportError("unterminated SMT-LIB command")


def _assertion_commands(source):
    commands = []
    checked, requested_proof, exited = False, False, False
    for tokens, text in _commands(source):
        name = tokens[1]
        if exited:
            raise ProofExportError("commands after exit are not supported")
        if name in ("check-sat", "get-proof", "exit"):
            if tokens != ["(", name, ")"]:
                raise ProofExportError("%s must have no arguments" % name)
            if name == "check-sat":
                if checked:
                    raise ProofExportError("only one check-sat query is supported")
                checked = True
            elif name == "get-proof":
                if not checked or requested_proof:
                    raise ProofExportError("get-proof must occur once, after check-sat")
                requested_proof = True
            else:
                exited = True
        elif name in _ASSERTION_COMMANDS or name == "set-option":
            if checked:
                raise ProofExportError("commands changing the problem after check-sat are not supported")
            if name == "set-option":
                if tokens != ["(", "set-option", ":produce-proofs", "true", ")"]:
                    raise ProofExportError("only (set-option :produce-proofs true) is supported")
            else:
                commands.append(text)
        else:
            raise ProofExportError("unsupported SMT-LIB command: %s" % name)
    # Z3's assertion parser ignores queries; validate them before removing them.
    return "\n".join(commands)


def _is_numeral(expr):
    return z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_ANUM


def numeral_value(expr):
    """Return the exact rational value of a Real numeral."""
    if not _is_numeral(expr):
        raise ProofExportError("expected a numeral")
    return Fraction(str(expr.as_fraction()))


def constant_value(expr):
    """Return the rational value of a variable-free Real term, or None."""
    kind = expr.decl().kind()
    if kind == z3.Z3_OP_ANUM:
        return numeral_value(expr)
    if kind not in _ARITH_OPERATORS:
        return None
    values = [constant_value(child) for child in expr.children()]
    if any(value is None for value in values):
        return None
    if kind == z3.Z3_OP_ADD:
        return sum(values, Fraction(0))
    if kind == z3.Z3_OP_SUB:
        return values[0] - sum(values[1:], Fraction(0))
    if kind == z3.Z3_OP_UMINUS:
        return -values[0]
    if kind == z3.Z3_OP_MUL:
        result = Fraction(1)
        for value in values:
            result *= value
        return result
    if values[1] == 0:
        raise ProofExportError("division by zero")
    return values[0] / values[1]


def _require_linear_real(expr):
    """Reject Real terms outside the linear fragment with constant coefficients."""
    kind = expr.decl().kind()
    if kind == z3.Z3_OP_UNINTERPRETED:
        if expr.decl().arity() != 0:
            raise ProofExportError("uninterpreted functions are not supported: %s" % expr.decl().name())
    elif kind == z3.Z3_OP_ANUM:
        pass
    elif kind == z3.Z3_OP_MUL:
        if sum(1 for child in expr.children() if constant_value(child) is None) > 1:
            raise ProofExportError("nonlinear multiplication is not supported")
    elif kind == z3.Z3_OP_DIV:
        divisor = constant_value(expr.arg(1))
        if divisor is None or divisor == 0:
            raise ProofExportError("division is supported only by a nonzero constant")
    elif kind == z3.Z3_OP_ITE:
        raise ProofExportError("arithmetic ite is not supported")
    elif kind not in (z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS):
        raise ProofExportError("unsupported arithmetic operator: %s" % expr.decl().name())


def classify_fragment(assertions):
    """Return "propositional" or "qf_lra", rejecting everything else."""
    pending, seen, arithmetic = list(assertions), set(), False
    while pending:
        expr = pending.pop()
        if expr.get_id() in seen:
            continue
        seen.add(expr.get_id())
        if not z3.is_app(expr):
            raise ProofExportError("only quantifier-free expressions are supported")
        decl = expr.decl()
        if z3.is_bool(expr):
            if decl.kind() == z3.Z3_OP_UNINTERPRETED:
                if decl.arity() != 0:
                    raise ProofExportError("uninterpreted functions are not supported: %s" % decl.name())
            elif decl.kind() in _ARITH_PREDICATES:
                arithmetic = True
            elif decl.kind() not in _BOOLEAN_OPERATORS:
                raise ProofExportError("unsupported propositional operator: %s" % decl.name())
            if decl.kind() in (z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT) and not z3.is_bool(expr.arg(0)):
                arithmetic = True
            elif decl.kind() == z3.Z3_OP_ITE and not z3.is_bool(expr.arg(1)):
                raise ProofExportError("arithmetic ite is not supported")
        elif z3.is_real(expr):
            arithmetic = True
            _require_linear_real(expr)
        else:
            raise ProofExportError("unsupported sort: %s" % expr.sort())
        pending.extend(expr.children())
    return "qf_lra" if arithmetic else "propositional"


def _require_propositional(assertions):
    if classify_fragment(assertions) != "propositional":
        raise ProofExportError("arithmetic requires the clause-log exporter (fragment qf_lra)")


def parse_propositional_assertions(source, context):
    """Parse the supported assertion snapshot without running solver search."""
    assertions = z3.parse_smt2_string(_assertion_commands(source), ctx=context)
    _require_propositional(assertions)
    return assertions


def parse_assertions(source, context):
    """Parse the assertion snapshot and return it with its fragment name."""
    assertions = z3.parse_smt2_string(_assertion_commands(source), ctx=context)
    return assertions, classify_fragment(assertions)


def _encode_proof(assertions, proof):
    declarations, nodes = [], []
    declaration_ids, node_ids = {}, {}
    rule_counts = Counter()
    proof_sort = proof.sort()

    def sort_name(sort):
        if sort.kind() == z3.Z3_BOOL_SORT:
            return "Bool"
        if sort.eq(proof_sort):
            return "Proof"
        raise ProofExportError("unsupported native proof sort: %s" % sort)

    roots = list(assertions) + [proof]
    pending = [(expr, False) for expr in reversed(roots)]
    while pending:
        expr, expanded = pending.pop()
        if expr.get_id() in node_ids:
            continue
        if not z3.is_app(expr):
            raise ProofExportError("non-application terms in native proofs are not supported")
        if not expanded:
            pending.append((expr, True))
            pending.extend((child, False) for child in reversed(expr.children()))
            continue
        decl = expr.decl()
        if decl.get_id() not in declaration_ids:
            if decl.params():
                raise ProofExportError("native declaration parameters are not supported: %s" % decl.name())
            declaration_ids[decl.get_id()] = len(declarations)
            declarations.append({
                "kind": decl.kind(),
                "name": str(decl.name()),
                "domain": [sort_name(decl.domain(i)) for i in range(decl.arity())],
                "range": sort_name(decl.range()),
                "parameters": [],
            })
        node_ids[expr.get_id()] = len(nodes)
        nodes.append({
            "declaration": declaration_ids[decl.get_id()],
            "arguments": [node_ids[child.get_id()] for child in expr.children()],
        })
        if expr.sort().eq(proof_sort):
            rule_counts[str(decl.name())] += 1
    return {
        "declarations": declarations,
        "nodes": nodes,
        "assertions": [node_ids[expr.get_id()] for expr in assertions],
        "proof": node_ids[proof.get_id()],
        "rule_counts": dict(sorted(rule_counts.items())),
    }


class DagBuilder:
    """Encode z3 expressions and synthesized proof steps as one shared DAG.

    Declarations are keyed by kind, name, domain, range, and parameters; nodes
    by their z3 identity or by declaration and arguments. Both are therefore
    hash-consed, so repeated literals, clauses, and steps share one node.
    """

    _SORTS = {z3.Z3_BOOL_SORT: "Bool", z3.Z3_REAL_SORT: "Real"}

    def __init__(self):
        self.declarations, self.nodes = [], []
        self.rule_counts = Counter()
        self._declaration_ids, self._expression_nodes, self._synthetic_nodes = {}, {}, {}
        # z3 reuses AST identifiers once an expression is garbage collected, so
        # every expression keyed by identifier is kept alive here.
        self._alive = []

    def sort_name(self, sort):
        name = self._SORTS.get(sort.kind())
        if name is None:
            raise ProofExportError("unsupported native proof sort: %s" % sort)
        return name

    def declaration(self, kind, name, domain, range_name, parameters=()):
        key = (kind, name, tuple(domain), range_name, tuple(parameters))
        index = self._declaration_ids.get(key)
        if index is None:
            index = self._declaration_ids[key] = len(self.declarations)
            self.declarations.append({
                "kind": kind, "name": name, "domain": list(domain), "range": range_name,
                "parameters": list(parameters),
            })
        return index

    def rule(self, kind, name, premises, parameters=()):
        return self.declaration(kind, name, ("Proof",) * premises + ("Bool",), "Proof", parameters)

    def node(self, declaration, arguments):
        key = (declaration, tuple(arguments))
        index = self._synthetic_nodes.get(key)
        if index is None:
            index = self._synthetic_nodes[key] = len(self.nodes)
            self.nodes.append({"declaration": declaration, "arguments": list(arguments)})
            if self.declarations[declaration]["range"] == "Proof":
                self.rule_counts[self.declarations[declaration]["name"]] += 1
        return index

    def expression(self, root):
        """Add a Bool or Real z3 expression and return its node index."""
        pending = [(root, False)]
        while pending:
            expr, expanded = pending.pop()
            if expr.get_id() in self._expression_nodes:
                continue
            if not z3.is_app(expr):
                raise ProofExportError("non-application terms are not supported")
            if not expanded:
                pending.append((expr, True))
                pending.extend((child, False) for child in reversed(expr.children()))
                continue
            self._alive.append(expr)
            decl = expr.decl()
            name = str(decl.name())
            if decl.kind() == z3.Z3_OP_ANUM:
                name = str(numeral_value(expr))  # The numeral is the declaration's parameter.
            elif decl.params():
                raise ProofExportError("native declaration parameters are not supported: %s" % decl.name())
            domain = tuple(self.sort_name(decl.domain(i)) for i in range(decl.arity()))
            declaration = self.declaration(decl.kind(), name, domain, self.sort_name(expr.sort()))
            arguments = [self._expression_nodes[child.get_id()] for child in expr.children()]
            self._expression_nodes[expr.get_id()] = self.node(declaration, arguments)
        return self._expression_nodes[root.get_id()]

    def certificate(self, source, fragment, assertions, root, compact=False):
        nodes, declarations, counts = self.nodes, self.declarations, self.rule_counts
        if compact:
            needed, pending = set(), list(assertions) + [root]
            while pending:
                node = pending.pop()
                if node not in needed:
                    needed.add(node)
                    pending.extend(nodes[node]["arguments"])
            node_ids = {node: index for index, node in enumerate(sorted(needed))}
            used_decls = sorted({nodes[node]["declaration"] for node in needed})
            decl_ids = {decl: index for index, decl in enumerate(used_decls)}
            declarations = [declarations[decl] for decl in used_decls]
            nodes = [{"declaration": decl_ids[nodes[node]["declaration"]],
                      "arguments": [node_ids[arg] for arg in nodes[node]["arguments"]]}
                     for node in sorted(needed)]
            assertions = [node_ids[node] for node in assertions]
            root = node_ids[root]
            counts = Counter(declarations[node["declaration"]]["name"] for node in nodes
                             if declarations[node["declaration"]]["range"] == "Proof")
        return {
            "format": "z3-native-proof-dag",
            "format_version": 1,
            "z3_version": z3.get_full_version(),
            "fragment": fragment,
            "result": "unsat",
            "verification": "unverified",
            "source_smt2": source,
            "declarations": declarations,
            "nodes": nodes,
            "assertions": list(assertions),
            "proof": root,
            "rule_counts": dict(sorted(counts.items())),
        }


def linear_combination_refutes(constraints):
    """Decide whether linear constraints combine into a contradiction.

    Each constraint is (coefficient, relation, terms, constant) meaning
    sum(terms) + constant <relation> 0 with relation in "<=", "<", or "=".
    terms maps variable identifiers to rational coefficients. Inequalities are
    scaled by their nonnegative coefficients and added. Equalities may be used
    with any rational multiplier, as in Z3's own arithmetic checker, so their
    multipliers are solved for by exact Gaussian elimination rather than read
    from the hint.
    """
    total, constant, strict, equalities = {}, Fraction(0), False, []
    for coefficient, relation, terms, offset in constraints:
        if relation == "=":
            equalities.append((dict(terms), offset))
            continue
        if coefficient < 0:
            return False
        for variable, value in terms.items():
            total[variable] = total.get(variable, Fraction(0)) + coefficient * value
        constant += coefficient * offset
        strict = strict or (relation == "<" and coefficient != 0)
    # Reduce the equalities to row echelon form, then eliminate every pivot
    # variable from the inequality sum.
    pivots = []
    for terms, offset in equalities:
        terms, offset = dict(terms), offset
        for pivot, row_terms, row_offset in pivots:
            factor = terms.get(pivot, Fraction(0))
            if factor:
                for variable, value in row_terms.items():
                    terms[variable] = terms.get(variable, Fraction(0)) - factor * value
                offset -= factor * row_offset
        terms = {variable: value for variable, value in terms.items() if value != 0}
        if not terms:
            if offset != 0:
                return True  # The equalities alone are inconsistent.
            continue
        pivot = min(terms)
        scale = terms[pivot]
        terms = {variable: value / scale for variable, value in terms.items()}
        pivots.append((pivot, terms, offset / scale))
    for pivot, row_terms, row_offset in pivots:
        factor = total.get(pivot, Fraction(0))
        if factor:
            for variable, value in row_terms.items():
                total[variable] = total.get(variable, Fraction(0)) - factor * value
            constant -= factor * row_offset
    if any(value != 0 for value in total.values()):
        return False
    if not any(relation != "=" for _, relation, _, _ in constraints):
        return False  # Consistent equalities only.
    return constant > 0 or (strict and constant == 0)


def _certificate_from_proof(source, assertions, proof):
    if (not z3.is_app(proof) or z3.is_bool(proof) or proof.num_args() == 0
            or not z3.is_false(proof.arg(proof.num_args() - 1))):
        raise ProofExportError("the native proof does not conclude false")
    certificate = _encode_proof(assertions, proof)
    certificate.update({
        "format": "z3-native-proof-dag",
        "format_version": 1,
        "z3_version": z3.get_full_version(),
        "fragment": "propositional",
        "result": "unsat",
        "verification": "unverified",
        "source_smt2": source,
    })
    return certificate


def export_certificate(source):
    """Return a native proof bundle, not an independently verified verdict.

    The source is one SMT-LIB assertion snapshot with an optional final
    check-sat/get-proof pair. Unsupported input, sat, and unknown are errors.
    This is the legacy proof-object path and supports propositional input.
    """
    context = z3.Context(proof=True)
    assertions = parse_propositional_assertions(source, context)
    solver = z3.Solver(ctx=context)
    solver.add(assertions)
    result = solver.check()
    if result == z3.sat:
        raise ProofExportError("sat: no unsat proof exists")
    if result == z3.unknown:
        raise ProofExportError("unknown: %s" % solver.reason_unknown())
    return _certificate_from_proof(source, assertions, solver.proof())


def default_z3_executable():
    """Locate the z3 executable: $Z3_EXE, then build/z3 next to this checkout, then PATH."""
    candidate = os.environ.get("Z3_EXE")
    if candidate:
        return candidate
    build = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                         "build", "z3")
    if os.access(build, os.X_OK):
        return build
    return "z3"


def export_clause_log_certificate(source, z3_executable=None, timeout=None):
    """Return a native-style proof bundle built from a sat.smt clause log.

    The z3 executable solves the assertions with sat.smt=true and preprocessing
    disabled, logging every assumed, inferred, and deleted clause. The log is
    rebuilt into the proof DAG format: theory hints become th-lemma nodes and
    reverse-unit-propagation steps become explicit resolution chains. The
    bundle is unverified; the Lean reconstructor must check it.
    """
    import proof_clause_log
    context = z3.Context()
    assertions, fragment = parse_assertions(source, context)
    try:
        text = proof_clause_log.run_clause_log(
            z3_executable or default_z3_executable(), _assertion_commands(source), timeout)
        text = proof_clause_log.trim_clause_log(z3_executable or default_z3_executable(), text, timeout)
        return proof_clause_log.build_certificate(source, fragment, assertions, text, context)
    except subprocess.TimeoutExpired:
        raise ProofExportError("native proof trimming timed out") from None
    except proof_clause_log.ProofExportError as error:
        # Running this file as a script imports it twice; unify the error class.
        raise ProofExportError(str(error)) from None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", help="SMT-LIB input file, or - for standard input")
    parser.add_argument("--core", choices=("auto", "legacy", "clause-log"), default="auto",
                        help="proof source: the legacy proof object (propositional input only) or the "
                             "sat.smt clause log via the z3 executable (default: legacy when propositional)")
    parser.add_argument("--z3", help="z3 executable for the clause log (default: $Z3_EXE, build/z3, or z3)")
    parser.add_argument("--timeout", type=float, help="seconds allowed for the clause-log solver run")
    args = parser.parse_args()
    try:
        if args.file == "-":
            source = sys.stdin.read()
        else:
            with open(args.file, encoding="utf-8", newline="") as stream:
                source = stream.read()
        core = args.core
        if core == "auto":
            _, fragment = parse_assertions(source, z3.Context())
            core = "legacy" if fragment == "propositional" else "clause-log"
        if core == "legacy":
            certificate = export_certificate(source)
        else:
            certificate = export_clause_log_certificate(source, args.z3, args.timeout)
        json.dump(certificate, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    except (ProofExportError, z3.Z3Exception, OSError, UnicodeError) as error:
        parser.exit(2, "%s: error: %s\n" % (parser.prog, error))


if __name__ == "__main__":
    main()
