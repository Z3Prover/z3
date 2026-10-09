############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Rebuild sat.smt clause logs as native-style proof DAG certificates.
############################################
"""Turn a Z3 sat.smt clause log into the z3-native-proof-dag certificate format.

The log records the assumed clauses after simplification, every inferred
clause with its justification hint, and deletions. This module replays it
with exact bookkeeping: each assumption is tied back to an original assertion
by an explicit rewrite or conjunct selection, each hint becomes one theory
lemma over its own literals, and each reverse-unit-propagation step becomes a
resolution chain under temporary hypotheses. Nothing here verifies the
inferences; the Lean reconstructor does.
"""

from fractions import Fraction
import os
from pathlib import Path
import re
import subprocess
import tempfile
import warnings

import z3

from proof_certificate import (
    DagBuilder, ProofExportError, _ARITH_PREDICATES, _CNF_HINT, _COEFFICIENT_HINTS, _LITERAL_HINTS,
    _NO_PREPROCESSING, _TOKEN, constant_value, linear_combination_refutes, numeral_value,
)

_NUMERAL = re.compile(r"^[0-9]+(\.[0-9]+)?$")
_RESULTS = ("sat", "unsat", "unknown")
_TRIM_THRESHOLD = 1_000_000


def run_clause_log(z3_executable, assertion_text, timeout=None):
    """Solve with the sat.smt core and return the clause log text."""
    with tempfile.TemporaryDirectory(prefix="z3_clause_log_") as directory:
        log = os.path.join(directory, "proof.log")
        problem = os.path.join(directory, "input.smt2")
        Path(problem).write_text(
            '(set-option :sat.smt true)\n(set-option :solver.proof.log "%s")\n' % log
            + _NO_PREPROCESSING + assertion_text + "\n(check-sat)\n", encoding="utf-8")
        command = [z3_executable, problem]
        if timeout is not None:
            command.insert(1, "-T:%d" % max(1, int(timeout)))
        try:
            run = subprocess.run(command, capture_output=True, text=True)
        except OSError as error:
            raise ProofExportError("cannot run the z3 executable %s: %s" % (z3_executable, error))
        lines = [line.strip() for line in run.stdout.splitlines() if line.strip()]
        result = lines[-1] if lines else ""
        if result == "sat":
            raise ProofExportError("sat: no unsat proof exists")
        if result != "unsat":
            detail = result if result in _RESULTS else (run.stderr.strip() or result or "no output")[-500:]
            raise ProofExportError("the solver did not report unsat: %s" % detail)
        if not os.path.exists(log):
            raise ProofExportError("the solver did not write a clause log")
        return Path(log).read_text(encoding="utf-8")


def _sexpressions(text):
    """Parse the log into nested lists of tokens, one per top-level command."""
    stack, position = [[]], 0
    while position < len(text):
        match = _TOKEN.match(text, position)
        if match is None:
            raise ProofExportError("unsupported token in the clause log at character %d" % position)
        position = match.end()
        token = match.group()
        if token.isspace() or token.startswith(";"):
            continue
        if token == "(":
            stack.append([])
        elif token == ")":
            if len(stack) == 1:
                raise ProofExportError("unbalanced clause log")
            closed = stack.pop()
            stack[-1].append(closed)
        else:
            stack[-1].append(token)
    if len(stack) != 1:
        raise ProofExportError("unterminated clause log")
    return stack[0]


def _dependency_numbers(sexpr):
    if (not isinstance(sexpr, list) or len(sexpr) < 2 or sexpr[0] != "deps"
            or any(not isinstance(value, str) or not value.isdecimal() for value in sexpr[1:])):
        raise ProofExportError("malformed clause dependency annotation")
    return int(sexpr[1]), tuple(int(value) for value in sexpr[2:])


def _dependency_core(text):
    """Select the final empty clause's dependency closure, keeping proof hints."""
    commands = _sexpressions(text)
    definitions, entries = {}, {}
    last = None
    for command in commands:
        if not command:
            raise ProofExportError("empty command in trimmed clause log")
        if command[0] == "define-const":
            if len(command) != 4 or not isinstance(command[1], str) or command[1] in definitions:
                raise ProofExportError("malformed or duplicate trimmed-log definition")
            definitions[command[1]] = command
        elif command[0] in ("assume", "infer"):
            if len(command) < 2 or not isinstance(command[-1], str):
                raise ProofExportError("missing trimmed-log dependency annotation")
            definition = definitions.get(command[-1])
            if definition is None or definition[2] != "Proof":
                raise ProofExportError("undefined trimmed-log dependency annotation")
            ident, dependencies = _dependency_numbers(definition[3])
            if ident in entries:
                raise ProofExportError("duplicate clause dependency identifier")
            entries[ident] = command, dependencies
            last = ident
        elif command[0] != "declare-fun":
            raise ProofExportError("unsupported trimmed-log command: %s" % command[0])
    if last is None or entries[last][0][0] != "infer" or len(entries[last][0]) != 3:
        raise ProofExportError("trimmed clause log has no final empty clause")
    needed, visiting, ordered, pending = set(), set(), [], [(last, False)]
    while pending:
        ident, expanded = pending.pop()
        if expanded:
            visiting.remove(ident)
            needed.add(ident)
            ordered.append(ident)
        elif ident not in needed:
            if ident not in entries:
                raise ProofExportError("undefined clause dependency: %d" % ident)
            if ident in visiting:
                raise ProofExportError("cyclic clause dependencies")
            visiting.add(ident)
            pending.append((ident, True))
            pending.extend((dep, False) for dep in reversed(entries[ident][1]))
    required, pending = set(), [entries[ident][0] for ident in needed]
    while pending:
        part = pending.pop()
        if isinstance(part, list):
            pending.extend(part)
        elif part in definitions and part not in required:
            required.add(part)
            pending.append(definitions[part][3])

    def render(expr):
        return "(" + " ".join(render(arg) if isinstance(arg, list) else arg for arg in expr) + ")"

    result = []
    for command in commands:
        if command[0] == "declare-fun":
            result.append(render(command))
        elif command[0] == "define-const" and command[1] in required:
            result.append(render(command))
    result.extend(render(entries[ident][0]) for ident in ordered)
    return "\n".join(result) + "\n"


def trim_clause_log(z3_executable, text, timeout=None):
    """Reduce large logs with untrusted native dependencies; replay checks every retained step."""
    if len(text) < _TRIM_THRESHOLD:
        return text
    with tempfile.TemporaryDirectory(prefix="z3_clause_trim_") as directory:
        source = Path(directory) / "proof.smt2"
        source.write_text(text, encoding="utf-8")
        try:
            run = subprocess.run([str(z3_executable), "-smt2", "solver.proof.trim=true", str(source)],
                                 capture_output=True, text=True, timeout=timeout)
        except OSError as error:
            raise ProofExportError("cannot run native proof trimming: %s" % error) from error
        if run.returncode or "(error" in run.stdout:
            raise ProofExportError("native proof trimming failed: %s" % (run.stderr + run.stdout)[-2000:])
        if run.stderr.strip():
            warnings.warn("native proof trimming diagnostics:\n" + run.stderr[-2000:], RuntimeWarning)
        return _dependency_core(run.stdout)


def _symbol(token):
    if token.startswith("|") and token.endswith("|") and len(token) >= 2:
        return token[1:-1]
    return token


def _number(sexpr):
    if isinstance(sexpr, str):
        if not _NUMERAL.match(sexpr):
            raise ProofExportError("unsupported numeral in the clause log: %s" % sexpr)
        return Fraction(sexpr)
    if len(sexpr) == 2 and sexpr[0] == "-":
        return -_number(sexpr[1])
    if len(sexpr) == 3 and sexpr[0] == "/":
        divisor = _number(sexpr[2])
        if divisor == 0:
            raise ProofExportError("division by zero in the clause log")
        return _number(sexpr[1]) / divisor
    raise ProofExportError("unsupported numeral in the clause log")


class _Terms:
    """Build z3 expressions for log terms inside the context of the parsed input."""

    def __init__(self, context, assertions):
        self.context = context
        self.defined = {}
        self.hints = {}
        self.constants = {}
        pending, seen = list(assertions), set()
        while pending:
            expr = pending.pop()
            if expr.get_id() in seen:
                continue
            seen.add(expr.get_id())
            if z3.is_const(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                self.constants[str(expr.decl().name())] = expr
            pending.extend(expr.children())

    def _subtract(self, arguments):
        if len(arguments) == 2:
            return arguments[0] - arguments[1]
        array = (z3.Ast * len(arguments))(*[argument.as_ast() for argument in arguments])
        return z3.ArithRef(z3.Z3_mk_sub(self.context.ref(), len(arguments), array), self.context)

    def build(self, sexpr):
        if isinstance(sexpr, str):
            if sexpr in self.defined:
                return self.defined[sexpr]
            if sexpr == "true":
                return z3.BoolVal(True, self.context)
            if sexpr == "false":
                return z3.BoolVal(False, self.context)
            if _NUMERAL.match(sexpr):
                return z3.RealVal(str(Fraction(sexpr)), self.context)
            name = _symbol(sexpr)
            if name in self.constants:
                return self.constants[name]
            raise ProofExportError("the clause log uses an undeclared or fresh symbol: %s" % sexpr)
        if not sexpr:
            raise ProofExportError("empty application in the clause log")
        head, arguments = sexpr[0], [self.build(argument) for argument in sexpr[1:]]
        if not isinstance(head, str):
            raise ProofExportError("unsupported application head in the clause log")
        count = len(arguments)
        if head == "not" and count == 1:
            return z3.Not(arguments[0])
        if head == "or":
            return z3.Or(*arguments) if count != 1 else z3.Or(arguments)
        if head == "and":
            return z3.And(*arguments) if count != 1 else z3.And(arguments)
        if head == "=>" and count == 2:
            return z3.Implies(arguments[0], arguments[1])
        if head == "xor" and count == 2:
            return z3.Xor(arguments[0], arguments[1])
        if head == "ite" and count == 3:
            return z3.If(arguments[0], arguments[1], arguments[2])
        if head == "=" and count == 2:
            return arguments[0] == arguments[1]
        if head == "distinct" and count >= 2:
            return z3.Distinct(*arguments)
        if head == "+" and count >= 2:
            return z3.Sum(*arguments)
        if head == "*" and count >= 2:
            return z3.Product(*arguments)
        if head == "-" and count == 1:
            return -arguments[0]
        if head == "-" and count >= 2:
            return self._subtract(arguments)
        if head == "/" and count == 2:
            return arguments[0] / arguments[1]
        if head in ("<=", "<", ">=", ">") and count == 2:
            left, right = arguments
            return {"<=": left <= right, "<": left < right, ">=": left >= right, ">": left > right}[head]
        raise ProofExportError("unsupported operator in the clause log: %s" % head)

    def define(self, name, sort, sexpr):
        if name in self.defined or name in self.hints:
            raise ProofExportError("duplicate definition in the clause log: %s" % name)
        # Definitions stay referenced for the whole replay, so their identifiers are stable.
        if sort == "Proof":
            self.hints[name] = sexpr
            return
        expr = self.build(sexpr)
        if str(expr.sort()) != sort:
            raise ProofExportError("definition %s has sort %s, declared %s" % (name, expr.sort(), sort))
        self.defined[name] = expr

    def hint(self, sexpr):
        """Return (name, [(coefficient, literal)]) for a theory hint or None for rup."""
        if sexpr == "rup":
            return None
        if isinstance(sexpr, str):
            if sexpr not in self.hints:
                raise ProofExportError("undefined proof hint in the clause log: %s" % sexpr)
            sexpr = self.hints[sexpr]
        if not sexpr or not isinstance(sexpr[0], str):
            raise ProofExportError("malformed proof hint in the clause log")
        name, arguments = sexpr[0], sexpr[1:]
        if name in _COEFFICIENT_HINTS:
            if len(arguments) % 2:
                raise ProofExportError("%s hint needs coefficient-literal pairs" % name)
            pairs = [(_number(arguments[index]), self.build(arguments[index + 1]))
                     for index in range(0, len(arguments), 2)]
        elif name in _LITERAL_HINTS:
            pairs = []
            for argument in arguments:
                auxiliary = self.hints.get(argument) if isinstance(argument, str) else argument
                if name == "euf" and isinstance(auxiliary, list) and auxiliary[:1] in (["cc"], ["comm"]):
                    if len(auxiliary) != 2 or not z3.is_eq(self.build(auxiliary[1])):
                        raise ProofExportError("malformed euf congruence hint")
                    # These are proof annotations, not premises. Lean must derive
                    # the contradiction from the Boolean literals alone.
                    continue
                pairs.append((Fraction(1), self.build(argument)))
        else:
            raise ProofExportError("unsupported clause-log hint: %s" % name)
        if not pairs and name != "smt":
            raise ProofExportError("%s hint has no literals" % name)
        for _, literal in pairs:
            if not z3.is_bool(literal):
                raise ProofExportError("%s hint literal is not Boolean" % name)
        return name, pairs

    def dependencies(self, sexpr):
        if isinstance(sexpr, str) and sexpr in self.hints:
            hint = self.hints[sexpr]
            if isinstance(hint, list) and hint[:1] == ["deps"]:
                return _dependency_numbers(hint)
        return None


def _strip(literal):
    """Return (atom, polarity) for a literal with any number of negations."""
    polarity = True
    while z3.is_not(literal):
        literal, polarity = literal.arg(0), not polarity
    return literal, polarity


def _key(literal):
    atom, polarity = _strip(literal)
    return atom.get_id(), polarity


def _complement(literal):
    return literal.arg(0) if z3.is_not(literal) else z3.Not(literal)


def _tautology(literals):
    """A clause with true, not false, or complementary literals needs no source."""
    seen = {}
    for literal in literals:
        atom, polarity = _strip(literal)
        if z3.is_true(atom) and polarity or z3.is_false(atom) and not polarity:
            return True
        if seen.setdefault(atom.get_id(), polarity) != polarity:
            return True
    return False


def _linear(expr, terms=None, scale=Fraction(1)):
    """Return (variables -> coefficient, constant) for a linear Real term."""
    terms = {} if terms is None else terms
    kind = expr.decl().kind()
    value = constant_value(expr)
    if value is not None:
        return terms, scale * value
    if kind == z3.Z3_OP_UNINTERPRETED:
        terms[expr.get_id()] = terms.get(expr.get_id(), Fraction(0)) + scale
        return terms, Fraction(0)
    constant = Fraction(0)
    if kind == z3.Z3_OP_ADD:
        for child in expr.children():
            terms, part = _linear(child, terms, scale)
            constant += part
    elif kind == z3.Z3_OP_SUB:
        terms, constant = _linear(expr.arg(0), terms, scale)
        for child in expr.children()[1:]:
            terms, part = _linear(child, terms, -scale)
            constant += part
    elif kind == z3.Z3_OP_UMINUS:
        terms, constant = _linear(expr.arg(0), terms, -scale)
    elif kind == z3.Z3_OP_MUL:
        factor, variable = Fraction(1), None
        for child in expr.children():
            child_value = constant_value(child)
            if child_value is not None:
                factor *= child_value
            elif variable is None:
                variable = child
            else:
                raise ProofExportError("nonlinear multiplication is not supported")
        terms, constant = _linear(variable, terms, scale * factor)
    elif kind == z3.Z3_OP_DIV:
        divisor = constant_value(expr.arg(1))
        if divisor is None or divisor == 0:
            raise ProofExportError("division is supported only by a nonzero constant")
        terms, constant = _linear(expr.arg(0), terms, scale / divisor)
    else:
        raise ProofExportError("unsupported arithmetic term: %s" % expr.decl().name())
    return terms, constant


def _constraint(literal):
    """Return (relation, terms, constant) with sum(terms) + constant <relation> 0."""
    atom, polarity = _strip(literal)
    kind = atom.decl().kind()
    if kind not in _ARITH_PREDICATES and kind != z3.Z3_OP_EQ:
        raise ProofExportError("hint literal is not an arithmetic atom")
    left, right = atom.arg(0), atom.arg(1)
    if not z3.is_real(left):
        raise ProofExportError("hint literal is not a Real atom")
    if kind == z3.Z3_OP_EQ:
        if not polarity:
            raise ProofExportError("negated equalities cannot enter a linear combination")
        relation, first, second = "=", left, right
    else:
        if kind in (z3.Z3_OP_GE, z3.Z3_OP_GT):
            left, right, kind = right, left, {z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_GT: z3.Z3_OP_LT}[kind]
        strict = kind == z3.Z3_OP_LT
        if polarity:
            relation, first, second = ("<" if strict else "<="), left, right
        else:
            relation, first, second = ("<=" if strict else "<"), right, left
    terms, constant = _linear(first)
    terms, offset = _linear(second, terms, Fraction(-1))
    return relation, {k: v for k, v in terms.items() if v != 0}, constant + offset


def check_linear_hint(name, pairs):
    """Check Farkas combinations and the shape of implied-equality hints."""
    if name == "implied-eq":
        atom, polarity = _strip(pairs[-1][1])
        if polarity or not z3.is_eq(atom) or not z3.is_real(atom.arg(0)):
            raise ProofExportError("implied-eq hint must end in a Real disequality")
        _constraint(atom)
        pairs = pairs[:-1]
    constraints = []
    for coefficient, literal in pairs:
        relation, terms, constant = _constraint(literal)
        constraints.append((coefficient, relation, terms, constant))
    # Implied equality is not a Farkas contradiction: Lean proves that the
    # preceding literals imply the equality complementary to the last literal.
    if name != "implied-eq" and not linear_combination_refutes(constraints):
        raise ProofExportError("%s hint coefficients do not refute its literals" % name)


class _Normalizer:
    """Canonical keys for Boolean formulas over linear atoms, used to match assumptions."""

    def __init__(self):
        self.cache = {}  # (AST identifier, polarity) -> (expression kept alive, key)

    def key(self, expr):
        return self._key(expr, True)

    def _key(self, expr, polarity):
        index = expr.get_id(), polarity
        cached = self.cache.get(index)
        if cached is None:
            cached = self.cache[index] = (expr, self._compute_key(expr, polarity))
        return cached[1]

    def _compute_key(self, expr, polarity):
        kind = expr.decl().kind()
        if kind == z3.Z3_OP_NOT:
            return self._key(expr.arg(0), not polarity)
        if kind in (z3.Z3_OP_AND, z3.Z3_OP_OR):
            if (kind == z3.Z3_OP_AND) == polarity:
                tag = "and"
            else:
                tag = "or"
            parts = set()
            identity = ("true",) if tag == "and" else ("false",)
            absorbing = ("false",) if tag == "and" else ("true",)
            for child in expr.children():
                child_key = self._key(child, polarity)
                if child_key == absorbing:
                    return absorbing
                if child_key == identity:
                    continue
                if child_key[0] == tag:
                    parts.update(child_key[1])
                else:
                    parts.add(child_key)
            if not parts:
                return identity
            if len(parts) == 1:
                return next(iter(parts))
            return (tag, tuple(sorted(parts, key=repr)))
        if kind == z3.Z3_OP_IMPLIES:
            return self._key(z3.Or(z3.Not(expr.arg(0)), expr.arg(1)), polarity)
        if kind == z3.Z3_OP_TRUE:
            return ("true",) if polarity else ("false",)
        if kind == z3.Z3_OP_FALSE:
            return ("false",) if polarity else ("true",)
        if kind in _ARITH_PREDICATES or (kind == z3.Z3_OP_EQ and z3.is_real(expr.arg(0))):
            return self._atom(expr, polarity)
        if kind == z3.Z3_OP_DISTINCT and z3.is_real(expr.arg(0)) and expr.num_args() == 2:
            return self._atom(expr.arg(0) == expr.arg(1), not polarity)
        positive = (kind, tuple(self._key(child, True) for child in expr.children()),
                    str(expr.decl().name()) if kind == z3.Z3_OP_UNINTERPRETED else "")
        return positive if polarity else ("not", positive)

    def _atom(self, expr, polarity):
        relation, terms, constant = _constraint(expr)
        if not terms:
            holds = {"<=": constant <= 0, "<": constant < 0, "=": constant == 0}[relation]
            return ("true",) if holds == polarity else ("false",)
        first = min(terms)
        scale = abs(terms[first])
        if relation == "=" and terms[first] < 0:
            scale = -scale
        body = (tuple(sorted((variable, str(value / scale)) for variable, value in terms.items())),
                str(constant / scale))
        if relation == "=":
            key = ("eq", body)
            return key if polarity else ("not", key)
        if relation == "<=":
            return ("le", body) if polarity else ("not", ("le", body))
        # p < 0 is the negation of -p <= 0.
        negated = (tuple(sorted((variable, str(-value / scale)) for variable, value in terms.items())),
                   str(-constant / scale))
        return ("not", ("le", negated)) if polarity else ("le", negated)


def _conjuncts(expr, path=()):
    """Yield (formula, and-elim path) for every conjunct reachable through nested ands."""
    yield expr, path
    if expr.decl().kind() == z3.Z3_OP_AND:
        for child in expr.children():
            yield from _conjuncts(child, path + (child,))


class _Replay:
    def __init__(self, source, fragment, assertions, context):
        self.source, self.fragment, self.context = source, fragment, context
        self.assertions = list(assertions)
        self.dag = DagBuilder()
        self.assertion_nodes = [self.dag.expression(expr) for expr in self.assertions]
        self.normalizer = _Normalizer()
        self.assertions_by_id = {expr.get_id(): expr for expr in self.assertions}
        self.assumption_sources = [(assertion, conjunct, path) for assertion in self.assertions
                                   for conjunct, path in _conjuncts(assertion)]
        self.assumptions_by_key = None
        self.clauses = {}        # entry id -> (proof node, literal expressions)
        self.clause_keys = {}    # entry id -> precomputed literal keys for propagation
        self.literal_keys = {}   # AST id -> (literal kept alive, key)
        self.by_key = {}         # frozenset of literal keys -> [entry ids]
        self.occurrences = {}    # atom id -> set of entry ids
        self.units = {}          # atom id -> entry id of a unit clause
        self.empty = set()       # entry ids of empty clauses
        self.next_entry = 0
        self.root = None
        self.logged_clauses = {}
        self.trimmed = False
        self.asserted = self.dag.rule(z3.Z3_OP_PR_ASSERTED, "asserted", 0)
        self.hypothesis = self.dag.rule(z3.Z3_OP_PR_HYPOTHESIS, "hypothesis", 0)
        self.lemma = self.dag.rule(z3.Z3_OP_PR_LEMMA, "lemma", 1)
        self.mp = self.dag.rule(z3.Z3_OP_PR_MODUS_PONENS, "mp", 2)
        self.rewrite = self.dag.rule(z3.Z3_OP_PR_REWRITE, "rewrite", 0)
        self.and_elim = self.dag.rule(z3.Z3_OP_PR_AND_ELIM, "and-elim", 1)
        self.def_axiom = self.dag.rule(z3.Z3_OP_PR_DEF_AXIOM, "def-axiom", 0)
        self.gates = {}          # atom id -> atom, kept alive because z3 reuses identifiers
        self.gate_entries = {}   # atom id -> independently justified gate clauses
        self.alive = []          # every literal referenced by identifier-keyed tables

    # -- Boolean gate definitions ----------------------------------------

    def ensure_gates(self, literal):
        """Add the Tseitin clauses of every compound Boolean atom inside a literal.

        Z3's clause-log checker propagates through such definitions implicitly,
        so the log's rup steps may rely on them. Each gate clause is justified
        as a def-axiom, which the reconstructor proves independently.
        """
        pending = [literal]
        while pending:
            atom, _ = _strip(pending.pop())
            if atom.get_id() in self.gates or not z3.is_bool(atom):
                continue
            self.gates[atom.get_id()] = atom
            kind, args = atom.decl().kind(), atom.children()
            if kind == z3.Z3_OP_OR:
                clauses = [[z3.Not(atom)] + args] + [[atom, z3.Not(arg)] for arg in args]
            elif kind == z3.Z3_OP_AND:
                clauses = [[atom] + [z3.Not(arg) for arg in args]] + [[z3.Not(atom), arg] for arg in args]
            elif kind == z3.Z3_OP_IMPLIES:
                clauses = [[z3.Not(atom), z3.Not(args[0]), args[1]], [atom, args[0]], [atom, z3.Not(args[1])]]
            elif kind in (z3.Z3_OP_EQ, z3.Z3_OP_IFF) and z3.is_bool(args[0]):
                clauses = [[z3.Not(atom), z3.Not(args[0]), args[1]], [z3.Not(atom), args[0], z3.Not(args[1])],
                           [atom, args[0], args[1]], [atom, z3.Not(args[0]), z3.Not(args[1])]]
            elif kind == z3.Z3_OP_XOR:
                clauses = [[atom, z3.Not(args[0]), args[1]], [atom, args[0], z3.Not(args[1])],
                           [z3.Not(atom), args[0], args[1]], [z3.Not(atom), z3.Not(args[0]), z3.Not(args[1])]]
            elif kind == z3.Z3_OP_ITE:
                clauses = [[z3.Not(atom), z3.Not(args[0]), args[1]], [z3.Not(atom), args[0], args[2]],
                           [atom, z3.Not(args[0]), z3.Not(args[1])], [atom, args[0], z3.Not(args[2])]]
            else:
                continue
            pending.extend(args)
            entries = self.gate_entries[atom.get_id()] = []
            for clause in clauses:
                node = self.dag.node(self.def_axiom, [self.dag.expression(self.clause_formula(clause))])
                entries.append(self.add_clause(node, clause))

    # -- clause database -------------------------------------------------

    def clause_formula(self, literals):
        if not literals:
            return z3.BoolVal(False, self.context)
        if len(literals) == 1:
            return literals[0]
        return z3.Or(*literals)

    def literal_key(self, literal):
        ident = literal.get_id()
        cached = self.literal_keys.get(ident)
        if cached is None:
            cached = self.literal_keys[ident] = literal, _key(literal)
        return cached[1]

    def add_clause(self, node, literals):
        entry = self.next_entry
        self.next_entry += 1
        self.alive.extend(literals)
        self.clauses[entry] = (node, literals)
        self.clause_keys[entry] = tuple(self.literal_key(literal) for literal in literals)
        keys = frozenset(self.clause_keys[entry])
        self.by_key.setdefault(keys, []).append(entry)
        for atom, _ in keys:
            self.occurrences.setdefault(atom, set()).add(entry)
        if len(keys) == 1 and len(literals) == 1:
            self.units.setdefault(next(iter(keys))[0], entry)
        if not literals:
            self.empty.add(entry)
        return entry

    def delete_clause(self, literals):
        keys = frozenset(self.literal_key(literal) for literal in literals)
        entries = self.by_key.get(keys)
        if not entries:
            return  # Deleting an absent clause does not affect soundness.
        entry = entries.pop()
        _, stored = self.clauses.pop(entry)
        self.clause_keys.pop(entry)
        self.empty.discard(entry)
        for atom, _ in keys:
            self.occurrences[atom].discard(entry)
        if self.units.get(next(iter(keys))[0]) == entry:
            del self.units[next(iter(keys))[0]]
            for other in entries:
                if len(self.clauses[other][1]) == 1:
                    self.units[next(iter(keys))[0]] = other
                    break

    # -- assumptions -----------------------------------------------------

    def assume(self, literals):
        """Tie an assumed clause to an original assertion.

        In order of preference: the identical formula, an equivalent formula
        or conjunct (by canonical key, then by a bounded solver check) bridged
        with a rewrite, or an implying formula or conjunct bridged with a cnf
        theory lemma, for assertions that preprocessing split into clauses.
        Tautological clauses need no source and become def-axiom nodes.
        """
        formula = self.clause_formula(literals)
        if _tautology(literals):
            return self.dag.node(self.def_axiom, [self.dag.expression(formula)])
        assertion = self.assertions_by_id.get(formula.get_id())
        if assertion is not None:
            return self.dag.node(self.asserted, [self.dag.expression(assertion)])
        target = self.normalizer.key(formula)
        if self.assumptions_by_key is None:
            self.assumptions_by_key = {}
            for source in self.assumption_sources:
                self.assumptions_by_key.setdefault(self.normalizer.key(source[1]), source)
        source = self.assumptions_by_key.get(target)
        if source is not None:
            assertion, conjunct, path = source
            return self._derive_assumption(assertion, path, conjunct, formula)
        for assertion, conjunct, path in self.assumption_sources:
            if self._valid(conjunct == formula):
                return self._derive_assumption(assertion, path, conjunct, formula)
        for assertion, conjunct, path in self.assumption_sources:
            if self._valid(z3.Implies(conjunct, formula)):
                source = self._derive_assumption(assertion, path, conjunct, conjunct)
                return self._cnf_lemma([(source, conjunct)], literals)
        # Preprocessing may combine several assertions, for example into the empty clause.
        if self.assertions and self._valid(z3.Implies(z3.And(*self.assertions), formula)):
            sources = [(self.dag.node(self.asserted, [self.dag.expression(assertion)]), assertion)
                       for assertion in dict.fromkeys(self.assertions, None)]
            return self._cnf_lemma(sources, literals)
        raise ProofExportError("assumed clause does not match any original assertion: %s" % formula)

    def _cnf_lemma(self, sources, literals):
        """Derive a clause from source formulas that imply it, through a cnf theory lemma."""
        declaration = self.dag.rule(z3.Z3_OP_PR_TH_LEMMA, "th-lemma", 0, [_CNF_HINT])
        lemma_literals = [z3.Not(formula) for _, formula in sources] + list(literals)
        lemma = self.dag.node(declaration, [self.dag.expression(self.clause_formula(lemma_literals))])
        self.alive.extend(lemma_literals)
        return self._resolve(lemma, [node for node, _ in sources], lemma_literals, list(literals))

    def _valid(self, claim):
        solver = z3.Solver(ctx=self.context)
        solver.set("rlimit", 200000)
        solver.add(z3.Not(claim))
        return solver.check() == z3.unsat

    def _derive_assumption(self, assertion, path, conjunct, formula):
        node = self.dag.node(self.asserted, [self.dag.expression(assertion)])
        for step in path:
            node = self.dag.node(self.and_elim, [node, self.dag.expression(step)])
        if conjunct.get_id() != formula.get_id():
            equivalence = self.dag.node(self.rewrite, [self.dag.expression(conjunct == formula)])
            node = self.dag.node(self.mp, [node, equivalence, self.dag.expression(formula)])
        return node

    # -- inferences ------------------------------------------------------

    def infer(self, literals, hint, dependencies=None):
        """Justify one logged clause.

        farkas, bound, implied-eq, and euf hints list literals that are jointly
        contradictory, so the lemma is the clause of their complements. tseitin
        hints list the gate clause itself and become def-axiom nodes. alldiff
        clauses must follow from the original assertions, not from the hint.
        A bare smt hint claims the logged clause is a theory tautology. Whenever
        the lemma differs from the logged clause, the latter is derived from
        the lemma and the clause database by unit propagation.
        """
        if hint is None:
            return self.rup(literals, dependencies)
        name, pairs = hint
        if name in ("tseitin", "alldiff"):
            lemma_literals = [literal for _, literal in pairs]
            lemma = (self.assume(lemma_literals) if name == "alldiff" else
                     self.dag.node(self.def_axiom, [self.dag.expression(self.clause_formula(lemma_literals))]))
        else:
            if name in _COEFFICIENT_HINTS:
                check_linear_hint(name, pairs)
            parameters = [name]
            if name in _COEFFICIENT_HINTS:
                parameters.extend(str(coefficient) for coefficient, _ in pairs)
            lemma_literals = (list(literals) if name == "smt"
                              else [_complement(literal) for _, literal in pairs])
            declaration = self.dag.rule(z3.Z3_OP_PR_TH_LEMMA, "th-lemma", 0, parameters)
            lemma = self.dag.node(declaration, [self.dag.expression(self.clause_formula(lemma_literals))])
        if {self.literal_key(literal) for literal in lemma_literals} == {self.literal_key(literal) for literal in literals}:
            return lemma, lemma_literals
        entry = self.add_clause(lemma, lemma_literals)
        try:
            return self.rup(literals, None if dependencies is None else dependencies + [entry])
        finally:
            self.delete_clause(self.clauses[entry][1]) if entry in self.clauses else None

    def rup(self, literals, dependencies=None):
        """Derive a clause by unit propagation, as hypotheses, resolutions, and a lemma."""
        assigned = {}  # atom id -> (polarity, proof node)
        queue = []
        units, empty, occurrences = self.units, self.empty, self.occurrences
        if dependencies is not None:
            units, empty, occurrences = {}, set(), {}
            selected = set(dependencies)
            pending = ([self.literal_key(literal)[0] for literal in literals]
                       + [key[0] for entry in selected for key in self.clause_keys[entry]])
            seen = set()
            while pending:
                atom = pending.pop()
                if atom in seen:
                    continue
                seen.add(atom)
                for entry in self.gate_entries.get(atom, ()):
                    if entry not in selected:
                        selected.add(entry)
                        pending.extend(key[0] for key in self.clause_keys[entry])
            for entry in sorted(selected):
                _, stored = self.clauses[entry]
                if not stored:
                    empty.add(entry)
                elif len(stored) == 1:
                    units.setdefault(self.clause_keys[entry][0][0], entry)
                for atom, _ in self.clause_keys[entry]:
                    occurrences.setdefault(atom, set()).add(entry)

        def assign(atom, polarity, node):
            assigned[atom] = (polarity, node)
            queue.append(atom)

        conflict = None
        if empty:
            conflict = self.clauses[min(empty)][0]
        for literal in literals:
            if conflict is not None:
                break
            complement = _complement(literal)
            atom, polarity = self.literal_key(complement)
            node = self.dag.node(self.hypothesis, [self.dag.expression(complement)])
            if atom in assigned:
                if assigned[atom][0] != polarity:
                    # The clause contains complementary literals.
                    conflict = self._resolve(node, [assigned[atom][1]], [complement], [])
                    break
                continue
            assign(atom, polarity, node)
        for atom, entry in list(units.items()):
            if conflict is not None:
                break
            node, stored = self.clauses[entry]
            polarity = self.clause_keys[entry][0][1]
            if atom not in assigned:
                assign(atom, polarity, node)
            elif assigned[atom][0] != polarity:
                conflict = self._resolve(node, [assigned[atom][1]], stored, [])
        while conflict is None and queue:
            atom = queue.pop()
            for entry in list(occurrences.get(atom, ())):
                node, stored = self.clauses[entry]
                false_nodes, open_literal, open_key = [], None, None
                for literal, key in zip(stored, self.clause_keys[entry]):
                    state = assigned.get(key[0])
                    if state is None:
                        if open_key is not None and open_key != key:
                            open_literal = None
                            break
                        open_literal, open_key = literal, key
                    elif state[0] == key[1]:
                        break  # satisfied clause
                    else:
                        false_nodes.append(state[1])
                else:
                    if open_key is None:
                        conflict = self._resolve(node, false_nodes, stored, [])
                        break
                    if open_literal is not None and false_nodes:
                        derived = self._resolve(node, false_nodes, stored, [open_literal])
                        assign(open_key[0], open_key[1], derived)
                    continue
                if conflict is not None:
                    break
        if conflict is None:
            raise ProofExportError("inferred clause is not derivable by unit propagation: %s"
                                   % self.clause_formula(literals))
        formula = self.clause_formula(literals)
        return self.dag.node(self.lemma, [conflict, self.dag.expression(formula)]), literals

    def _resolve(self, clause_node, unit_nodes, clause_literals, remaining):
        units = list(dict.fromkeys(unit_nodes))
        declaration = self.dag.rule(z3.Z3_OP_PR_UNIT_RESOLUTION, "unit-resolution", 1 + len(units))
        conclusion = self.clause_formula(remaining)
        return self.dag.node(declaration, [clause_node] + units + [self.dag.expression(conclusion)])

    # -- driver ----------------------------------------------------------

    def run(self, text):
        terms = _Terms(self.context, self.assertions)
        for command in _sexpressions(text):
            if not command or not isinstance(command[0], str):
                raise ProofExportError("malformed clause log command")
            head = command[0]
            annotation, dependencies = None, None
            if head in ("assume", "infer") and len(command) > 1:
                annotation = terms.dependencies(command[-1])
                if annotation is not None:
                    self.trimmed = True
                    ident, ids = annotation
                    if ident in self.logged_clauses or any(i not in self.logged_clauses for i in ids):
                        raise ProofExportError("duplicate or forward clause dependency")
                    dependencies = [self.logged_clauses[i] for i in ids]
                    command = command[:-1]
            if head == "declare-fun":
                if len(command) != 4 or not isinstance(command[1], str):
                    raise ProofExportError("malformed declaration in the clause log")
                if command[3] == "Proof":
                    continue
                if command[2] != [] or _symbol(command[1]) not in terms.constants:
                    raise ProofExportError("the clause log declares a symbol absent from the input: %s"
                                           % command[1])
            elif head == "define-const":
                if len(command) != 4 or not isinstance(command[1], str) or not isinstance(command[2], str):
                    raise ProofExportError("malformed definition in the clause log")
                terms.define(command[1], command[2], command[3])
            elif head == "assume":
                literals = [terms.build(part) for part in command[1:]]
                node = self.assume(literals)
                for literal in literals:
                    self.ensure_gates(literal)
                entry = self.add_clause(node, literals)
            elif head == "infer":
                if len(command) < 2:
                    raise ProofExportError("malformed inference in the clause log")
                hint = terms.hint(command[-1])
                literals = [terms.build(part) for part in command[1:-1]]
                for literal in literals + ([pair[1] for pair in hint[1]] if hint else []):
                    self.ensure_gates(literal)
                node, stored = self.infer(literals, hint, dependencies)
                if not literals:
                    self.root = node
                entry = self.add_clause(node, stored)
            elif head == "del":
                self.delete_clause([terms.build(part) for part in command[1:]])
            elif head in ("proofs", "set-option", "set-info", "set-logic"):
                continue
            else:
                raise ProofExportError("unsupported clause log command: %s" % head)
            if annotation is not None:
                self.logged_clauses[annotation[0]] = entry
        if self.root is None:
            # A contradiction found while asserting or during preprocessing is not
            # logged as an inference, and the log may even be empty. Derive the
            # empty clause by propagation, or tie it to the assertions directly.
            try:
                self.root, _ = self.rup([])
            except ProofExportError:
                self.root = self.assume([])
        return self.dag.certificate(self.source, self.fragment, self.assertion_nodes, self.root,
                                    compact=self.trimmed)


def build_certificate(source, fragment, assertions, text, context):
    """Rebuild a clause log as an unverified z3-native-proof-dag bundle."""
    return _Replay(source, fragment, assertions, context).run(text)
