############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Export native Boolean refutations for independent proof consumers.
############################################
"""Export an unverified native proof DAG for one propositional SMT-LIB problem."""

import argparse
from collections import Counter
import json
import re
import sys

import z3


class ProofExportError(Exception):
    """The input or native proof is outside the exporter's supported fragment."""


_TOKEN = re.compile(
    r'\s+|;[^\r\n]*|"(?:[^"]|"")*"|\|(?:\\.|[^|\\])*\||[()]|[^\s();"|#]+|#[xb][0-9a-fA-F]+',
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


def _require_propositional(assertions):
    pending, seen = list(assertions), set()
    while pending:
        expr = pending.pop()
        if expr.get_id() in seen:
            continue
        seen.add(expr.get_id())
        if not z3.is_app(expr) or not z3.is_bool(expr):
            raise ProofExportError("only quantifier-free propositional expressions are supported")
        decl = expr.decl()
        if decl.kind() == z3.Z3_OP_UNINTERPRETED:
            if decl.arity() != 0:
                raise ProofExportError("uninterpreted functions are not supported: %s" % decl.name())
        elif decl.kind() not in _BOOLEAN_OPERATORS:
            raise ProofExportError("unsupported propositional operator: %s" % decl.name())
        pending.extend(expr.children())


def parse_propositional_assertions(source, context):
    """Parse the supported assertion snapshot without running solver search."""
    assertions = z3.parse_smt2_string(_assertion_commands(source), ctx=context)
    _require_propositional(assertions)
    return assertions


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


def export_certificate(source):
    """Return a native proof bundle, not an independently verified verdict.

    The source is one SMT-LIB assertion snapshot with an optional final
    check-sat/get-proof pair. Unsupported input, sat, and unknown are errors.
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
    proof = solver.proof()
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", help="SMT-LIB input file, or - for standard input")
    args = parser.parse_args()
    try:
        if args.file == "-":
            source = sys.stdin.read()
        else:
            with open(args.file, encoding="utf-8", newline="") as stream:
                source = stream.read()
        certificate = export_certificate(source)
        json.dump(certificate, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    except (ProofExportError, z3.Z3Exception, OSError, UnicodeError) as error:
        parser.exit(2, "%s: error: %s\n" % (parser.prog, error))


if __name__ == "__main__":
    main()
