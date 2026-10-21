############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Export native Boolean, linear real arithmetic, and uninterpreted-function
# refutations for independent proof consumers.
############################################
"""Export an unverified native proof DAG for one propositional, QF_LRA, QF_LIA, QF_UF, QF_UFLRA, or QF_UFLIA SMT-LIB problem.

Two proof sources: the legacy proof object of the smt core and the sat.smt
clause log, both for every fragment; the integer ones (QF_LIA, QF_UFLIA,
including div and mod by a numeral and abs) are opt-in on both, since the
integer solver's cuts are certified by Lean alone. An incremental script
(push, pop, reset, several check-sat queries, assumptions) is certified one
query at a time: the certificate is about the assertions in scope at the
selected query (see query_snapshot).
"""

import argparse
from collections import Counter
from fractions import Fraction
import json
import math
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
    "set-logic", "set-info", "declare-sort", "define-sort", "declare-const", "declare-fun", "define-fun",
    "assert",
}
# The queries a certificate can be about; a script may have several (see
# query_snapshot), and Z3 reads the arguments of check-sat as assumptions.
_QUERIES = {"check-sat", "check-sat-using", "check-sat-assuming"}
# Queries that only print: accepted anywhere (one argument), or after the
# check-sat they report on (no arguments), and dropped like get-proof. The
# exporter runs its own solver, so they are never answered here.
_INFORMATION_QUERIES = {"get-info", "get-option", "echo"}
_RESULT_QUERIES = {"get-proof", "get-model", "get-unsat-core", "get-assignment"}
# set-option commands accepted and ignored, by Z3's parameter name with "-"
# and "_" identified. The certificate is a statement about the parsed
# assertions that Lean checks, so an option that only configures Z3's output,
# model production, resource limits, or search cannot change what is
# certified; these are the ones seen in SMT-LIB benchmarks and z3test's
# regressions. Anything else is rejected rather than ignored: options that
# change how the input is read (numeral-as-real, int-real-coercions,
# smtlib2_compliant, which makes Z3's scanner read "-1.0" as a symbol and
# disables Int/Real coercions, and rewriter.*) would certify a different
# reading of the input than Z3's, and the proof-production options the
# exporter sets itself (sat.smt, solver.proof.*, smt.clause_proof, the
# preprocessing switches of _NO_PREPROCESSING, combined_solver.*) select the
# evidence the exporter controls.
_IGNORED_OPTIONS = frozenset({
    # Output, models, and cores.
    "print_success", "print_warning", "produce_models", "produce_assignments", "produce_unsat_cores",
    "unsat_core", "produce_proofs", "proof", "model", "model_validate", "interactive_mode",
    "verbose", "stats", "type_check",
    # Resource limits and search configuration.
    "auto_config", "random_seed", "timeout", "rlimit", "reproducible_resource_limit",
    "smt.auto_config", "smt.arith.solver", "smt.random_seed", "smt.phase_selection",
    "smt.arith.random_initial_value", "smt.arith.eager_eq_axioms", "smt.arith.propagation_mode",
    "smt.mbqi", "smt.ematching", "smt.macro_finder", "smt.relevancy", "smt.theory_aware_branching",
    "smt.threads", "smt.case_split", "smt.delay_units", "smt.delay_units_threshold",
    "smt.restart_factor", "smt.restart_strategy", "smt.qi.cost", "smt.qi.eager_threshold",
    "smt.core.minimize", "sat.local_search", "sat.prob_search", "sat.random_seed",
    "nlsat.inline_vars", "nlsat.randomize", "parallel.enable", "tactic.default_tactic",
})
# Printing and model-presentation families, every member output-only.
_IGNORED_OPTION_PREFIXES = ("pp.", "model.")
_INPUT_READING_OPTIONS = ("numeral_as_real", "int_real_coercions", "smtlib2_compliant", "rewriter.")
# Certificate sort names with a fixed meaning; an uninterpreted sort keeps its
# own name, which Z3's parser already keeps distinct from the built-in sorts.
_RESERVED_SORTS = ("Bool", "Real", "Int", "Proof")
_BOOLEAN_OPERATORS = {
    z3.Z3_OP_TRUE, z3.Z3_OP_FALSE, z3.Z3_OP_NOT, z3.Z3_OP_AND, z3.Z3_OP_OR,
    z3.Z3_OP_IMPLIES, z3.Z3_OP_XOR, z3.Z3_OP_IFF, z3.Z3_OP_EQ,
    z3.Z3_OP_DISTINCT, z3.Z3_OP_ITE,
}
# Linear real arithmetic: atoms over Real terms built from variables, numerals,
# sums, differences, negation, scaling by a numeral, division by a numeral,
# and Real-valued ite, whose value is a linear term under either branch.
# Linear integer arithmetic is the same fragment over Int without Real
# division, plus the integer div and mod by a nonzero numeral and abs, which
# are opaque atoms of the linear forms (Z3's arithmetic solver axiomatizes
# div and mod by explicit clauses, see proof_clause_log, and rewrites abs to
# an ite); to_real and to_int are rejected, and Int never mixes with Real.
_ARITH_PREDICATES = {z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT}
_ARITH_OPERATORS = {z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS, z3.Z3_OP_MUL, z3.Z3_OP_DIV}
_ARITH_NAMES = {
    z3.Z3_OP_LE: "<=", z3.Z3_OP_GE: ">=", z3.Z3_OP_LT: "<", z3.Z3_OP_GT: ">",
    z3.Z3_OP_ADD: "+", z3.Z3_OP_SUB: "-", z3.Z3_OP_UMINUS: "-", z3.Z3_OP_MUL: "*",
    z3.Z3_OP_DIV: "/", z3.Z3_OP_IDIV: "div", z3.Z3_OP_MOD: "mod", z3.Z3_OP_ABS: "abs",
}
# Clause-log hint encodings; replay handles each hint's clause convention.
# cut is the integer solver's hint for a Gomory cut or a gcd conflict: its
# pairs name the bounds the cut rests on, but no coefficients certify the
# rounding, so the clause is shape-checked here and proved by Lean alone,
# like euf.
_COEFFICIENT_HINTS = ("farkas", "bound", "implied-eq", "cut")
# The fragments over Int, certified through the clause log and Lean alone
# (see parse_assertions).
_INTEGER_FRAGMENTS = ("qf_lia", "qf_uflia")
# arith is the hint of the arithmetic solver's own axioms (the div and mod
# definitions): like euf it lists jointly contradictory literals, and like cut
# it is shape-checked here and proved by Lean alone.
_LITERAL_HINTS = ("euf", "tseitin", "smt", "alldiff", "arith")
# Synthesized by the exporter, not logged by Z3: an original assertion implies
# one of the clauses it was split into.
_CNF_HINT = "cnf"
# Hints of the legacy core's (_ th-lemma arith <hint> coefficients...) steps
# and the certificate hint each becomes. theory_lra labels LP conflicts
# farkas, bound propagations bound, and equality propagations implied-eq, with
# one coefficient per premise and per literal of the concluding clause;
# arith_eq_adapter's axioms tying an equality to its two inequalities are
# triangle-eq. The older theory_arith (smt.arith.solver=2, which the
# frontend's tactic preamble used to select for difference-logic input)
# labels its propagations assign-bounds and eq-propagate and weights the
# antecedents only, so the propagated literal's weight of 1 is added here.
# Over Int, theory_lra's cuts and its div/mod axioms are bare (_ th-lemma
# arith) steps, kept as the arith hint (see _th_lemma_parameters); any other
# hint name (nla, gomory-cut, gcd-test) is rejected.
_LEGACY_HINTS = {
    "farkas": "farkas", "bound": "bound", "assign-bounds": "bound",
    "implied-eq": "implied-eq", "eq-propagate": "implied-eq", "triangle-eq": "triangle-eq",
}
# The clause log starts after preprocessing, so every pass that rewrites one
# assertion using another is disabled. bound_simplifier runs solve_eqs and
# propagate_values internally regardless of their own options. The smt.*
# options reach the core's own simplifiers only: for a non-incremental
# check-sat the frontend's combined solver first runs the tactic of the
# input's logic (simplify, propagate-values, ctx-simplify, solve-eqs, and
# elim-uncnstr for logics without a dedicated tactic, QF_UFLRA among them),
# whose passes ignore the smt.* options, introduce fresh k!N constants for
# unconstrained subterms, and Ackermannize uninterpreted predicates over
# Bool. combined_solver.ignore_solver1 sends the assertions to the sat.smt
# core directly, so the log refers to the input's own symbols. The legacy
# exporter sets the same option on its solver (see export_certificate).
_NO_PREPROCESSING = (
    "(set-option :combined_solver.ignore_solver1 true)\n"
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


def _check_option(tokens):
    """Reject a set-option command unless ignoring it leaves the certified statement unchanged."""
    if len(tokens) != 5 or not tokens[2].startswith(":"):
        raise ProofExportError("set-option takes one keyword and one value")
    option = tokens[2][1:].replace("-", "_")
    if option.startswith(_INPUT_READING_OPTIONS):
        raise ProofExportError("option %s changes how the input is read and is not supported" % tokens[2])
    if option not in _IGNORED_OPTIONS and not option.startswith(_IGNORED_OPTION_PREFIXES):
        raise ProofExportError("option %s is not supported; only output, model, resource, and search "
                               "options are ignored" % tokens[2])


def _scope_count(tokens):
    """Return the numeral argument of a push or pop command (1 when absent)."""
    if len(tokens) == 3:
        return 1
    if len(tokens) == 4 and tokens[2].isdigit():
        return int(tokens[2])
    raise ProofExportError("%s takes at most one numeral" % tokens[1])


def _is_symbol(token):
    """Whether a token is an SMT-LIB symbol (simple or quoted), not a numeral, keyword, string, or parenthesis."""
    return token not in ("(", ")") and not token.startswith((":", '"', "#")) and not token[0].isdigit()


def _check_sort_definition(tokens):
    """Reject a define-sort command that is not (define-sort name (parameters) sort).

    Z3's parser expands every use of the alias, substituting the parameters,
    so the parsed assertions, the clause log, and the certificate mention
    only the expanded sorts, which are checked like any other; Z3 also rejects
    an unknown sort in the body and a name already declared or defined. The
    shape is checked here so that the exporter, not a later stage, rejects a
    malformed definition, and repeated parameters are rejected because Z3
    accepts them without a defined meaning.
    """
    malformed = ProofExportError("define-sort takes a name, a parenthesized list of parameters, and one sort")
    if len(tokens) < 7 or not _is_symbol(tokens[2]) or tokens[3] != "(" or ")" not in tokens[4:]:
        raise malformed
    close = tokens.index(")", 4)
    parameters, body = tokens[4:close], tokens[close + 1:-1]
    if not all(_is_symbol(parameter) for parameter in parameters):
        raise malformed
    if len(set(parameters)) != len(parameters):
        raise ProofExportError("define-sort %s repeats a parameter" % tokens[2])
    if len(body) == 1:
        if not _is_symbol(body[0]):
            raise malformed
        return
    # A parenthesized sort application: the command is balanced, so the body
    # is one sort exactly when its first parenthesis closes at its last token.
    depth = 0
    for index, token in enumerate(body):
        depth += {"(": 1, ")": -1}.get(token, 0)
        if depth <= 0 and index != len(body) - 1:
            raise malformed
    if not body or body[0] != "(" or depth != 0:
        raise malformed


def _assumption_commands(tokens):
    """Return the assumptions of a check-sat query as assert commands.

    check-sat-assuming lists them in parentheses; Z3 also takes them as the
    arguments of check-sat. The exporter does not restrict them to literals:
    Z3's parser type-checks each one as an assertion of the snapshot, and the
    certified theorem states them next to the asserted formulas.
    """
    terms = tokens[2:-1]
    if tokens[1] == "check-sat-assuming":
        if len(terms) < 2 or terms[0] != "(" or terms[-1] != ")":
            raise ProofExportError("check-sat-assuming takes a parenthesized list of assumptions")
        terms = terms[1:-1]
    commands, start, depth = [], 0, 0
    for index, token in enumerate(terms):
        if token == "(":
            depth += 1
        elif token == ")":
            depth -= 1
            if depth < 0:
                # "(check-sat-assuming (p) (q))": the list closed early.
                raise ProofExportError("check-sat-assuming takes a parenthesized list of assumptions")
        if depth == 0:
            commands.append("(assert %s)" % " ".join(terms[start:index + 1]))
            start = index + 1
    return commands


def query_snapshot(source, query=None):
    """Return the assertion snapshot of one check-sat query of an SMT-LIB script.

    The result is (commands, index, count): the declarations, definitions,
    and assertions in scope at the selected query, as SMT-LIB text without
    the queries, the zero-based index of that query among the script's
    check-sat, check-sat-using, and check-sat-assuming commands, and the
    number of such commands. push, pop, reset, and reset-assertions are
    replayed as Z3 does with its default of scoped declarations: a
    declaration or define-sort alias made inside a popped scope is gone with
    its assertions,
    reset-assertions removes every assertion but keeps the declarations and
    the open scopes (cmd_context::reset_assertions), and reset clears
    everything. The assumptions
    of a query are part of its snapshot, so the certified theorem is that
    the assertions in scope together with the assumptions are contradictory.
    With query None the script must have at most one query; a script
    without any is one query over its final state. The certificate records
    the index, and the reconstructor rebuilds the same snapshot from the
    original input, so the statement Lean checks is a statement about the
    selected query, never about the certificate's own copy of it.
    """
    if query is not None and (type(query) is not int or query < 0):
        raise ProofExportError("the query index must be a nonnegative integer")
    scopes = [[]]
    snapshot, count = None, 0
    checked, requested_proof, exited = False, False, False
    for tokens, text in _commands(source):
        name = tokens[1]
        if exited:
            raise ProofExportError("commands after exit are not supported")
        if name in _QUERIES:
            # The tactic only configures Z3's search; the exporter runs its own
            # solver and Lean checks the result, so it is validated no further.
            if name == "check-sat-using" and len(tokens) < 4:
                raise ProofExportError("check-sat-using must name a tactic")
            if query is None or query == count:
                commands = [command for scope in scopes for _, command in scope]
                if name != "check-sat-using":
                    commands.extend(_assumption_commands(tokens))
                snapshot = "\n".join(commands)
            count += 1
            checked, requested_proof = True, False
        elif name in _RESULT_QUERIES or name == "exit":
            if tokens != ["(", name, ")"]:
                raise ProofExportError("%s must have no arguments" % name)
            if name == "exit":
                exited = True
            elif name == "get-proof":
                if not checked or requested_proof:
                    raise ProofExportError("get-proof must occur once, after check-sat")
                requested_proof = True
            elif not checked:
                raise ProofExportError("%s must occur after check-sat" % name)
        elif name in _INFORMATION_QUERIES:
            if len(tokens) != 4:
                raise ProofExportError("%s takes one argument" % name)
        elif name == "push":
            scopes.extend([] for _ in range(_scope_count(tokens)))
        elif name == "pop":
            depth = _scope_count(tokens)
            if depth >= len(scopes):
                raise ProofExportError("pop %d exceeds the %d open scopes" % (depth, len(scopes) - 1))
            del scopes[len(scopes) - depth:]
        elif name == "reset":
            if tokens != ["(", name, ")"]:
                raise ProofExportError("reset must have no arguments")
            # Z3 forgets the last result too: get-model after reset fails.
            scopes, checked, requested_proof = [[]], False, False
        elif name == "reset-assertions":
            # As in Z3 (not SMT-LIB's "pop every scope"): the assertions go,
            # the declarations and the scope stack stay, and a later pop
            # still drops the declarations of its scope.
            if tokens != ["(", name, ")"]:
                raise ProofExportError("reset-assertions must have no arguments")
            scopes = [[entry for entry in scope if entry[0] != "assert"] for scope in scopes]
        elif name == "set-option":
            _check_option(tokens)
        elif name in _ASSERTION_COMMANDS:
            if name == "declare-sort" and tokens[3:] not in ([")"], ["0", ")"]):
                raise ProofExportError("only uninterpreted sorts of arity 0 are supported")
            if name == "define-sort":
                _check_sort_definition(tokens)
            scopes[-1].append((name, text))
        else:
            raise ProofExportError("unsupported SMT-LIB command: %s" % name)
    if count == 0 and query in (None, 0):
        # Z3's assertion parser ignores queries; validate them before removing them.
        return "\n".join(command for scope in scopes for _, command in scope), 0, 0
    if query is None and count > 1:
        raise ProofExportError("the script has %d check-sat queries; select one by its zero-based index "
                               "(--query)" % count)
    if snapshot is None:
        raise ProofExportError("the script has %d check-sat %s, so query %d does not exist"
                               % (count, "query" if count == 1 else "queries", query))
    return snapshot, (0 if query is None else query), count


def _assertion_commands(source, query=None):
    return query_snapshot(source, query)[0]


def _is_numeral(expr):
    return z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_ANUM


def numeral_value(expr):
    """Return the exact rational value of a Real or Int numeral."""
    if not _is_numeral(expr):
        raise ProofExportError("expected a numeral")
    if z3.is_int_value(expr):
        return Fraction(int(expr.as_string()))
    return Fraction(str(expr.as_fraction()))


def constant_value(expr):
    """Return the rational value of a variable-free Real or Int term, or None."""
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


def integer_divisor(expr):
    """Return the nonzero constant divisor of an Int div or mod term, rejecting any other.

    SMT-LIB leaves div and mod by zero uninterpreted, while Lean's Int
    division and remainder are total functions (x / 0 = 0), so a proof over
    them would cover one interpretation only; a nonconstant divisor is
    nonlinear. Away from zero the two agree: SMT-LIB's div and mod are
    Euclidean (0 <= mod < |divisor|), as Lean's Int / and % are.
    """
    divisor = constant_value(expr.arg(1))
    if divisor is None or divisor == 0:
        raise ProofExportError("integer %s is supported only by a nonzero constant" % expr.decl().name())
    return divisor


def _require_linear_arithmetic(expr):
    """Reject Real or Int terms outside the linear fragment with constant coefficients.

    Real division is accepted by a nonzero constant, integer div and mod by a
    nonzero constant, and abs over Int; rem and the conversions between Int
    and Real are distinct operators that fall through to the rejection.
    """
    kind = expr.decl().kind()
    if kind == z3.Z3_OP_ABS and not z3.is_int(expr):
        # SMT-LIB defines abs on Int only. Z3 accepts a Real abs, which the
        # reconstructor rejects, so the exporter rejects it as unsupported.
        raise ProofExportError("unsupported arithmetic operator: abs over Real")
    if kind in (z3.Z3_OP_UNINTERPRETED, z3.Z3_OP_ANUM, z3.Z3_OP_ABS):
        pass  # Variables, applications of uninterpreted functions, and abs are the atoms of linear forms.
    elif kind == z3.Z3_OP_MUL:
        if sum(1 for child in expr.children() if constant_value(child) is None) > 1:
            raise ProofExportError("nonlinear multiplication is not supported")
    elif kind == z3.Z3_OP_DIV:
        divisor = constant_value(expr.arg(1))
        if divisor is None or divisor == 0:
            raise ProofExportError("division is supported only by a nonzero constant")
    elif kind in (z3.Z3_OP_IDIV, z3.Z3_OP_MOD):
        integer_divisor(expr)
    elif kind not in (z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS, z3.Z3_OP_ITE):
        raise ProofExportError("unsupported arithmetic operator: %s" % expr.decl().name())


def is_uninterpreted_sort(sort):
    return sort.kind() == z3.Z3_UNINTERPRETED_SORT


def _require_uninterpreted_sort(candidate, sorts):
    """Check an uninterpreted sort's name and record it in sorts.

    Any number of uninterpreted sorts is accepted: the Lean encoding renders
    them all as one type, which is sound for unsatisfiability (see the
    exporter README), while the certificate keeps every sort name so the
    reconstructor can check that the proof is well-sorted.
    """
    if candidate.name() in _RESERVED_SORTS:
        raise ProofExportError("unsupported uninterpreted sort name: %s" % candidate.name())
    sorts.add(candidate.name())


def _require_uninterpreted_signature(decl, sorts):
    """Check that a function or predicate ranges over uninterpreted sorts, Bool, Real, and Int only.

    Arguments may be Bool, Real, or Int as well as uninterpreted sorts (Lean
    injects a Boolean or numeric argument into the carrier); the result is
    Bool, Real, Int, or a sort. Returns (real, integer): whether the signature
    mentions Real, which makes the input QF_UFLRA, or Int, which makes it
    QF_UFLIA (never both: a signature mixing them is rejected by the caller).
    """
    candidates = [decl.domain(i) for i in range(decl.arity())] + [decl.range()]
    real = integer = False
    for candidate in candidates:
        if candidate.kind() == z3.Z3_BOOL_SORT:
            continue
        if candidate.kind() == z3.Z3_REAL_SORT:
            real = True
            continue
        if candidate.kind() == z3.Z3_INT_SORT:
            integer = True
            continue
        if not is_uninterpreted_sort(candidate):
            raise ProofExportError("uninterpreted functions over %s are not supported: %s" % (
                candidate, decl.name()))
        _require_uninterpreted_sort(candidate, sorts)
    return real, integer


def _require_unique_symbol(decl, symbols):
    """Reject one symbol name declared with several signatures.

    Z3 accepts such overloading and tells the declarations apart by sort, but
    the certificate binds symbols by name: the reconstructor's comparison with
    the input is faithful only if every name denotes one symbol of the input.
    """
    name = str(decl.name())
    if not symbols.setdefault(name, decl).eq(decl):
        raise ProofExportError("symbol declared with several signatures: %s" % name)


def classify_fragment(assertions):
    """Return "propositional", "qf_lra", "qf_lia", "qf_uf", "qf_uflra", or "qf_uflia", rejecting everything else."""
    pending, seen, real, integer, sorts, symbols = list(assertions), set(), False, False, set(), {}
    functions = False  # whether any uninterpreted function or predicate is applied
    while pending:
        expr = pending.pop()
        if expr.get_id() in seen:
            continue
        seen.add(expr.get_id())
        if not z3.is_app(expr):
            raise ProofExportError("only quantifier-free expressions are supported")
        decl = expr.decl()
        if decl.kind() == z3.Z3_OP_UNINTERPRETED:
            _require_unique_symbol(decl, symbols)
            if decl.arity() != 0:
                functions = True
                signature_real, signature_integer = _require_uninterpreted_signature(decl, sorts)
                real, integer = real or signature_real, integer or signature_integer
        if z3.is_bool(expr):
            if decl.kind() == z3.Z3_OP_UNINTERPRETED:
                pass
            elif decl.kind() not in _ARITH_PREDICATES and decl.kind() not in _BOOLEAN_OPERATORS:
                raise ProofExportError("unsupported propositional operator: %s" % decl.name())
            if decl.kind() in _ARITH_PREDICATES or decl.kind() in (z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT):
                real = real or z3.is_real(expr.arg(0))
                integer = integer or z3.is_int(expr.arg(0))
        elif z3.is_arith(expr):
            real, integer = real or z3.is_real(expr), integer or z3.is_int(expr)
            _require_linear_arithmetic(expr)
        elif is_uninterpreted_sort(expr.sort()):
            # Constants, function applications, and ite, whose branches are
            # terms of the sort and whose condition is any formula.
            if decl.kind() in (z3.Z3_OP_UNINTERPRETED, z3.Z3_OP_ITE):
                _require_uninterpreted_sort(expr.sort(), sorts)
            else:
                raise ProofExportError("unsupported operator over an uninterpreted sort: %s" % decl.name())
        else:
            raise ProofExportError("unsupported sort: %s" % expr.sort())
        pending.extend(expr.children())
    if integer:
        # Linear integer arithmetic: the Lean encoding values the variables in
        # Int and the integer solver's rounding steps are proved there, on its
        # own (QF_LIA) or next to uninterpreted sorts and functions (QF_UFLIA,
        # the Int valuation next to the carrier, into which Int arguments are
        # injected like Bool ones). Mixed Int/Real input (QF_LIRA) has no
        # encoding yet.
        if real:
            raise ProofExportError("mixing integer and real arithmetic is not supported")
        return "qf_uflia" if sorts or functions else "qf_lia"
    if sorts or functions:
        # Uninterpreted sorts and functions mixed with linear real arithmetic
        # are QF_UFLRA: the Lean encoding carries the Rat valuation next to the
        # carrier, into which Real arguments are injected like Bool ones.
        # Predicates over Bool alone are the qf_uf fragment without a sort: the
        # Lean encoding injects their arguments into the carrier like any other
        # Bool argument.
        return "qf_uflra" if real else "qf_uf"
    return "qf_lra" if real else "propositional"


def _require_legacy_fragment(assertions, integer=False):
    """Return the fragment if the legacy proof object can certify it.

    The legacy core's equality proofs (congruence, transitivity, symmetry) are
    complete, and theory_lra records the Farkas coefficients of its conflicts
    and bound propagations as th-lemma parameters, so every real-valued
    fragment is supported; a th-lemma without coefficients is rejected when
    the proof is encoded. The integer fragments are opt-in as in
    parse_assertions: the integer solver's cuts are bare (_ th-lemma arith)
    steps without coefficients, certified by Lean alone.
    """
    fragment = classify_fragment(assertions)
    if fragment in _INTEGER_FRAGMENTS and not integer:
        raise ProofExportError("integer arithmetic (%s) is certified by Lean alone; "
                               "the consumer must accept the fragment explicitly" % fragment)
    return fragment


def parse_legacy_assertions(source, context, integer=False, query=None):
    """Parse the assertion snapshot for the legacy proof object, with its fragment name."""
    assertions = z3.parse_smt2_string(_assertion_commands(source, query), ctx=context)
    return assertions, _require_legacy_fragment(assertions, integer)


def parse_propositional_assertions(source, context, query=None):
    """Parse a propositional assertion snapshot without running solver search."""
    assertions, fragment = parse_legacy_assertions(source, context, query=query)
    if fragment != "propositional":
        raise ProofExportError("uninterpreted functions are not propositional (fragment %s)" % fragment)
    return assertions


def parse_assertions(source, context, integer=False, query=None):
    """Parse the assertion snapshot and return it with its fragment name.

    The snapshot is that of the script's only check-sat query, or of the
    query selected by its zero-based index (see query_snapshot). The integer
    fragments (qf_lia, qf_uflia) are opt-in: the integer solver's
    cut steps (and Farkas steps resting on cuts) carry no coefficient
    certificate that the replay can re-derive, so they are certified by Lean
    alone and a consumer accepts them explicitly. The exporter and the
    reconstructor do; a harness that classifies input for other proof
    checkers keeps the previous fragments.
    """
    assertions = z3.parse_smt2_string(_assertion_commands(source, query), ctx=context)
    fragment = classify_fragment(assertions)
    if fragment in _INTEGER_FRAGMENTS and not integer:
        raise ProofExportError("integer arithmetic (%s) is certified through the clause log and Lean alone; "
                               "the consumer must accept the fragment explicitly" % fragment)
    return assertions, fragment


def _th_lemma_parameters(decl, premises, conclusion=None, integer=False):
    """Return the certificate parameters of a native th-lemma declaration applied to premises.

    The legacy core labels the step (_ th-lemma arith <hint> c1 ... cn). In
    the certificate, farkas and bound coefficients weight the premises in
    order and then the literals of the concluding clause; implied-eq and
    triangle-eq steps carry none, since Lean proves those implications
    outright. Only magnitudes enter a Farkas combination (theory_arith records
    the sign of the row coefficient), and the reconstructor re-derives the
    combination, so the coefficients are hints, not trusted. A bare
    (_ th-lemma arith) records no evidence: over Real it is rejected; over
    Int it is theory_lra's own axiom (a div or mod definition, a clause
    without premises) or a cut (the bound literal a Gomory or Hermite cut
    derives from the premises it lists), both shape-checked by the
    reconstructor and proved by Lean alone like the clause log's arith and
    cut hints. Indexed LP steps use their local weights; input and discharge
    bridges and integer rounding steps are re-proved by Lean.
    """
    parameters = decl.params()
    if integer and len(parameters) == 1 and parameters[0] == "arith":
        return ["arith"]
    if (len(parameters) >= 2 and parameters[0] == "arith"
            and isinstance(parameters[1], str) and parameters[1].startswith("lp-")):
        rule = parameters[1]
        integer_rule = integer and rule in ("lp-integer-tighten", "lp-integer-lattice", "lp-gomory")
        if rule not in ("lp-input", "lp-linear", "lp-discharge") and not integer_rule:
            raise ProofExportError("th-lemma without a replayable theory hint: %s" % rule)
        try:
            index = Fraction(str(parameters[2]))
            if index.denominator != 1 or not 0 <= index < 2**32 - 1:
                raise ValueError()
        except (IndexError, ValueError, ZeroDivisionError):
            raise ProofExportError("invalid LP step index") from None
        if integer_rule:
            if len(parameters) != 3 or conclusion is None:
                raise ProofExportError("invalid %s inference" % rule)
            return ["farkas" if z3.is_false(conclusion) else "arith"]
        if rule != "lp-linear":
            if len(parameters) != 3 or (premises not in (0, 1) if rule == "lp-input" else premises != 1):
                raise ProofExportError("invalid %s inference" % rule)
            return ["smt"]
        if conclusion is None:
            raise ProofExportError("missing LP linear conclusion")
        if len(parameters) != 3 + premises + (not z3.is_false(conclusion)):
            raise ProofExportError("invalid LP linear coefficient count")
        hint = ("farkas" if z3.is_false(conclusion) else
                "implied-eq" if z3.is_eq(conclusion) else "bound")
        parameters = ["arith", hint] + parameters[3:]
    if len(parameters) < 2 or parameters[0] != "arith" or parameters[1] not in _LEGACY_HINTS:
        raise ProofExportError("th-lemma without a replayable theory hint: %s" % " ".join(
            str(parameter) for parameter in parameters))
    coefficients = []
    for parameter in parameters[2:]:
        try:
            coefficients.append(abs(Fraction(str(parameter))))
        except (ValueError, ZeroDivisionError):
            raise ProofExportError("th-lemma coefficient is not a rational: %s" % parameter) from None
    hint = _LEGACY_HINTS[parameters[1]]
    if parameters[1] == "assign-bounds" and coefficients:
        # theory_arith weights the antecedents only. The propagated literal
        # has weight 1; it is the first clause literal when the step has no
        # premises and the conclusion when it has.
        coefficients = coefficients + [Fraction(1)] if premises else [Fraction(1)] + coefficients
    if hint == "implied-eq":
        coefficients = []  # never summed; the reconstructor checks shapes and Lean proves the equality
        if not premises and conclusion is not None and z3.is_eq(conclusion):
            hint = "smt"
    return [hint] + [str(coefficient) for coefficient in coefficients]


def _integer_coefficients_certify(step, hint, coefficients):
    """Whether a legacy farkas or bound step over Int re-derives from its coefficients.

    theory_lra labels every LP conflict farkas and every LP bound propagation
    bound, over Int too, where the explanation may rest on bounds the solver
    tightened to the integer lattice or on a lattice conflict (no integer
    point on the rationally feasible region), which no rational combination
    of the premises shows. As for the clause log (check_linear_hint), such a
    step keeps no coefficients: the reconstructor shape-checks it and Lean
    proves it alone. A step whose literals are not linear atoms keeps its
    coefficients, so that the reconstructor rejects it with its own message.
    """
    import proof_clause_log
    arguments = _proof_arguments(step)
    premises, conclusion = arguments[:-1], arguments[-1]
    literals = ([] if z3.is_false(conclusion) else list(conclusion.children()) if z3.is_or(conclusion)
                else [conclusion])
    if len(coefficients) != len(premises) + len(literals):
        return True
    constraints = []  # _constraint takes a literal that holds: a premise, or a denied clause literal's complement
    try:
        for coefficient, premise in zip(coefficients, premises):
            constraints.append((coefficient,) + proof_clause_log._constraint(premise.arg(premise.num_args() - 1)))
        for coefficient, literal in zip(coefficients[len(premises):], literals):
            constraints.append((coefficient,) + proof_clause_log._constraint(proof_clause_log._complement(literal)))
    except (ProofExportError, proof_clause_log.ProofExportError, z3.Z3Exception):
        return True
    return linear_combination_refutes(constraints) or (hint == "bound" and bound_combination_refutes(constraints))


def _proof_arguments(expr):
    """Remove the nonlogical LP context; Lean re-proves every remaining inference."""
    arguments = expr.children()
    if expr.decl().kind() != z3.Z3_OP_PR_TH_LEMMA:
        return arguments
    parameters = expr.decl().params()
    if (len(parameters) < 2 or parameters[0] != "arith"
            or not isinstance(parameters[1], str) or not parameters[1].startswith("lp-")):
        return arguments
    if len(arguments) < 2:
        raise ProofExportError("missing LP context")
    context = arguments[0]
    if (context.decl().kind() != z3.Z3_OP_PR_TH_LEMMA
            or context.decl().params()[:2] != ["arith", "lp-context"]
            or context.num_args() != 1 or not z3.is_true(context.arg(0))):
        raise ProofExportError("invalid LP context")
    return arguments[1:]


def _encode_proof(assertions, proof, integer=False):
    declarations, nodes = [], []
    declaration_ids, node_ids = {}, {}
    rule_counts = Counter()
    proof_sort = proof.sort()

    def sort_name(sort):
        if sort.kind() == z3.Z3_BOOL_SORT:
            return "Bool"
        if sort.kind() == z3.Z3_REAL_SORT:
            return "Real"
        if sort.kind() == z3.Z3_INT_SORT:
            return "Int"
        if sort.eq(proof_sort):
            return "Proof"
        if is_uninterpreted_sort(sort) and sort.name() not in _RESERVED_SORTS:
            return sort.name()  # The certificate keeps the input's own sort name.
        raise ProofExportError("unsupported native proof sort: %s" % sort)

    roots = list(assertions) + [proof]
    pending = [(expr, False) for expr in reversed(roots)]
    while pending:
        expr, expanded = pending.pop()
        if expr.get_id() in node_ids:
            continue
        if not z3.is_app(expr):
            raise ProofExportError("non-application terms in native proofs are not supported")
        arguments = _proof_arguments(expr)
        if not expanded:
            pending.append((expr, True))
            pending.extend((child, False) for child in reversed(arguments))
            continue
        decl = expr.decl()
        name, parameters = str(decl.name()), []
        if decl.kind() == z3.Z3_OP_ANUM:
            name = str(numeral_value(expr))  # The numeral is the declaration's parameter.
        elif decl.kind() == z3.Z3_OP_PR_TH_LEMMA:
            parameters = _th_lemma_parameters(decl, len(arguments) - 1, arguments[-1], integer=integer)
            if integer and parameters[0] in ("farkas", "bound") and len(parameters) > 1 and \
                    not _integer_coefficients_certify(expr, parameters[0], [Fraction(c) for c in parameters[1:]]):
                parameters = parameters[:1]  # One declaration per step shape: Lean alone proves this one.
        elif decl.params():
            raise ProofExportError("native declaration parameters are not supported: %s" % decl.name())
        key = (decl.get_id(), tuple(parameters))
        if key not in declaration_ids:
            declaration_ids[key] = len(declarations)
            declarations.append({
                "kind": decl.kind(),
                "name": name,
                "domain": [sort_name(decl.domain(i))
                           for i in range(expr.num_args() - len(arguments), decl.arity())],
                "range": sort_name(decl.range()),
                "parameters": parameters,
            })
        node_ids[expr.get_id()] = len(nodes)
        nodes.append({
            "declaration": declaration_ids[key],
            "arguments": [node_ids[child.get_id()] for child in arguments],
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

    _SORTS = {z3.Z3_BOOL_SORT: "Bool", z3.Z3_REAL_SORT: "Real", z3.Z3_INT_SORT: "Int"}

    def __init__(self):
        self.declarations, self.nodes = [], []
        self.rule_counts = Counter()
        self._declaration_ids, self._expression_nodes, self._synthetic_nodes = {}, {}, {}
        # z3 reuses AST identifiers once an expression is garbage collected, so
        # every expression keyed by identifier is kept alive here.
        self._alive = []

    def sort_name(self, sort):
        name = self._SORTS.get(sort.kind())
        if name is None and is_uninterpreted_sort(sort) and sort.name() not in _RESERVED_SORTS:
            name = sort.name()  # The certificate keeps the input's own sort name.
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
        """Add a Bool, Real, or uninterpreted-sort z3 expression and return its node index."""
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

    def certificate(self, source, fragment, assertions, root, compact=False, query=0):
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
            "format_version": 2,
            "z3_version": z3.get_full_version(),
            "fragment": fragment,
            "result": "unsat",
            "verification": "unverified",
            "source_smt2": source,
            "query": query,
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
    pivots = _echelon(equalities)
    if pivots is None:
        return True  # The equalities alone are inconsistent.
    total, constant = _eliminate(pivots, total, constant)
    if total:
        return False
    if not any(relation != "=" for _, relation, _, _ in constraints):
        return False  # Consistent equalities only.
    return constant > 0 or (strict and constant == 0)


def _echelon(equalities):
    """Reduce (terms, offset) equalities to row echelon form; None if they are inconsistent."""
    pivots = []
    for terms, offset in equalities:
        terms, offset = _eliminate(pivots, dict(terms), offset)
        if not terms:
            if offset != 0:
                return None
            continue
        pivot = min(terms)
        scale = terms[pivot]
        terms = {variable: value / scale for variable, value in terms.items()}
        pivots.append((pivot, terms, offset / scale))
    return pivots


def _eliminate(pivots, terms, constant):
    """Substitute every pivot variable out of terms + constant; zero coefficients are dropped."""
    terms = dict(terms)
    for pivot, row_terms, row_offset in pivots:
        factor = terms.get(pivot, Fraction(0))
        if factor:
            for variable, value in row_terms.items():
                terms[variable] = terms.get(variable, Fraction(0)) - factor * value
            constant -= factor * row_offset
    return {variable: value for variable, value in terms.items() if value != 0}, constant


def integer_tightened(relation, terms, constant):
    """Strengthen a strict constraint over integer-valued terms: t < 0 is t + 1 <= 0.

    The step is sound only when every coefficient and the constant are
    integers, so that t takes integer values; the integer fragment has no
    division and integer numerals only, and anything else is rejected.
    """
    if relation != "<":
        return relation, terms, constant
    if constant.denominator != 1 or any(value.denominator != 1 for value in terms.values()):
        raise ProofExportError("strict integer constraint with fractional coefficients")
    return "<=", terms, constant + 1


def _rounded(terms, constant):
    """Round sum(terms) + constant <= 0 to the integer lattice.

    With integer coefficients of gcd g and integer-valued variables, the sum
    is a multiple of g, so the constant can be raised to the next multiple of
    g and the row divided by g (Z3's checker calls this step cut).
    """
    scale = 1
    for value in list(terms.values()) + [constant]:
        scale = scale * value.denominator // math.gcd(scale, value.denominator)
    terms = {variable: value * scale for variable, value in terms.items()}
    constant *= scale
    divisor = 0
    for value in terms.values():
        divisor = math.gcd(divisor, abs(int(value)))
    if divisor <= 1:
        return terms, constant
    return ({variable: value / divisor for variable, value in terms.items()},
            Fraction(math.ceil(constant / divisor)))


def bound_combination_refutes(constraints):
    """Decide an integer bound propagation, mirroring Z3's clause-log checker.

    constraints are as in linear_combination_refutes, already tightened to
    non-strict form, with the denied consequent last. The other inequalities
    are summed with their coefficients, the equalities eliminated from the
    sum and from the consequent, the sum rounded to the integer lattice, and
    the consequent added with the multiplier that cancels one shared
    variable (Z3 recomputes it rather than reading it from the hint). Every
    step is a consequence over integer-valued variables, so no variable left
    and a positive constant is a contradiction.
    """
    if len(constraints) < 2 or any(relation == "<" for _, relation, _, _ in constraints):
        return False
    *premises, (_, consequent_relation, consequent_terms, consequent_constant) = constraints
    if consequent_relation == "=":
        return False
    equalities = [(dict(terms), offset) for _, relation, terms, offset in premises if relation == "="]
    total, constant = {}, Fraction(0)
    for coefficient, relation, terms, offset in premises:
        if relation == "=":
            continue
        if coefficient < 0:
            return False
        for variable, value in terms.items():
            total[variable] = total.get(variable, Fraction(0)) + coefficient * value
        constant += coefficient * offset
    pivots = _echelon(equalities)
    if pivots is None:
        return True
    total, constant = _eliminate(pivots, total, constant)
    consequent_terms, consequent_constant = _eliminate(pivots, consequent_terms, consequent_constant)
    if not consequent_terms:
        return consequent_constant > 0
    if not total:
        return constant > 0
    total, constant = _rounded(total, constant)
    for variable in sorted(total):
        if variable not in consequent_terms:
            continue
        multiplier = abs(consequent_terms[variable] / total[variable])
        combined = dict(consequent_terms)
        for other, value in total.items():
            combined[other] = combined.get(other, Fraction(0)) + multiplier * value
        if all(value == 0 for value in combined.values()) and consequent_constant + multiplier * constant > 0:
            return True
    return False


def _certificate_from_proof(source, assertions, proof, query=0):
    if (not z3.is_app(proof) or z3.is_bool(proof) or proof.num_args() == 0
            or not z3.is_false(proof.arg(proof.num_args() - 1))):
        raise ProofExportError("the native proof does not conclude false")
    fragment = _require_legacy_fragment(assertions, integer=True)
    certificate = _encode_proof(assertions, proof, fragment in _INTEGER_FRAGMENTS)
    certificate.update({
        "format": "z3-native-proof-dag",
        "format_version": 2,
        "z3_version": z3.get_full_version(),
        "fragment": fragment,
        "result": "unsat",
        "verification": "unverified",
        "source_smt2": source,
        "query": query,
    })
    return certificate


def export_certificate(source, query=None):
    """Return a native proof bundle, not an independently verified verdict.

    The source is an SMT-LIB script; the certificate is about the assertion
    snapshot of its only check-sat query, or of the query selected by its
    zero-based index (see query_snapshot). Unsupported input, sat, and
    unknown are errors.
    This is the legacy proof-object path (the smt core, sat.smt=false) and
    supports every fragment; theory_lra's th-lemma steps carry their Farkas
    coefficients as declaration parameters, except over Int, where cuts, the
    div/mod axioms, and lattice conflicts carry none and Lean proves them.
    """
    context = z3.Context(proof=True)
    assertions, _ = parse_legacy_assertions(source, context, integer=True, query=query)
    _, index, _ = query_snapshot(source, query)
    solver = z3.Solver(ctx=context)
    # The default solver runs the tactic of the input's logic first (see
    # _NO_PREPROCESSING); its elim-uncnstr pass names unconstrained subterms
    # by intro-def steps over fresh k!N constants, which the certificate
    # rejects. Send the assertions to the smt core directly.
    solver.set("combined_solver.ignore_solver1", True)
    solver.add(assertions)
    result = solver.check()
    if result == z3.sat:
        raise ProofExportError("sat: no unsat proof exists")
    if result == z3.unknown:
        raise ProofExportError("unknown: %s" % solver.reason_unknown())
    return _certificate_from_proof(source, assertions, solver.proof(), index)


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


def export_clause_log_certificate(source, z3_executable=None, timeout=None, query=None):
    """Return a native-style proof bundle built from a sat.smt clause log.

    The z3 executable solves the assertions of the selected query (see
    export_certificate) with sat.smt=true, the frontend's
    tactic preamble bypassed, and preprocessing disabled (_NO_PREPROCESSING),
    logging every assumed, inferred, and deleted clause. The log is rebuilt
    into the proof DAG format: theory hints become th-lemma nodes and
    reverse-unit-propagation steps become explicit resolution chains. The
    bundle is unverified; the Lean reconstructor must check it.
    """
    import proof_clause_log
    context = z3.Context()
    assertions, fragment = parse_assertions(source, context, integer=True, query=query)
    commands, index, _ = query_snapshot(source, query)
    try:
        text = proof_clause_log.run_clause_log(z3_executable or default_z3_executable(), commands, timeout)
        text = proof_clause_log.trim_clause_log(z3_executable or default_z3_executable(), text, timeout)
        certificate = proof_clause_log.build_certificate(source, fragment, assertions, text, context)
        certificate["query"] = index
        return certificate
    except subprocess.TimeoutExpired:
        raise ProofExportError("native proof trimming timed out") from None
    except proof_clause_log.ProofExportError as error:
        # Running this file as a script imports it twice; unify the error class.
        raise ProofExportError(str(error)) from None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", help="SMT-LIB input file, or - for standard input")
    parser.add_argument("--core", choices=("auto", "legacy", "clause-log"), default="auto",
                        help="proof source: the legacy proof object (propositional, QF_UF, QF_LRA, or QF_UFLRA "
                             "input) or the sat.smt clause log via the z3 executable (default: legacy when "
                             "propositional, clause log otherwise)")
    parser.add_argument("--z3", help="z3 executable for the clause log (default: $Z3_EXE, build/z3, or z3)")
    parser.add_argument("--timeout", type=float, help="seconds allowed for the clause-log solver run")
    parser.add_argument("--query", type=int,
                        help="zero-based index of the check-sat query to certify in an incremental script "
                             "(push, pop, reset, several queries); default: the script's only query")
    args = parser.parse_args()
    try:
        if args.file == "-":
            source = sys.stdin.read()
        else:
            with open(args.file, encoding="utf-8", newline="") as stream:
                source = stream.read()
        core = args.core
        if core == "auto":
            _, fragment = parse_assertions(source, z3.Context(), integer=True, query=args.query)
            core = "legacy" if fragment == "propositional" else "clause-log"
        if core == "legacy":
            certificate = export_certificate(source, args.query)
        else:
            certificate = export_clause_log_certificate(source, args.z3, args.timeout, args.query)
        json.dump(certificate, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    except (ProofExportError, z3.Z3Exception, OSError, UnicodeError) as error:
        parser.exit(2, "%s: error: %s\n" % (parser.prog, error))


if __name__ == "__main__":
    main()
