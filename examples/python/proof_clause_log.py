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

import z3

from proof_certificate import (
    DagBuilder, ProofExportError, _ARITH_PREDICATES, _CNF_HINT, _COEFFICIENT_HINTS, _LITERAL_HINTS,
    _NO_PREPROCESSING, _TOKEN, constant_value, linear_combination_refutes, numeral_value,
)

_NUMERAL = re.compile(r"^[0-9]+(\.[0-9]+)?$")
_RESULTS = ("sat", "unsat", "unknown")


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
            pairs = [(Fraction(1), self.build(argument)) for argument in arguments]
        else:
            raise ProofExportError("unsupported clause-log hint: %s" % name)
        if not pairs and name != "smt":
            raise ProofExportError("%s hint has no literals" % name)
        for _, literal in pairs:
            if not z3.is_bool(literal):
                raise ProofExportError("%s hint literal is not Boolean" % name)
        return name, pairs


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
        self.cache = {}  # AST identifier -> (expression kept alive, key)

    def key(self, expr):
        cached = self.cache.get(expr.get_id())
        if cached is None:
            cached = self.cache[expr.get_id()] = (expr, self._key(expr, True))
        return cached[1]

    def _key(self, expr, polarity):
        kind = expr.decl().kind()
        if kind == z3.Z3_OP_NOT:
            return self._key(expr.arg(0), not polarity)
        if kind in (z3.Z3_OP_AND, z3.Z3_OP_OR):
            if (kind == z3.Z3_OP_AND) == polarity:
                tag = "and"
            else:
                tag = "or"
            parts = set()
            for child in expr.children():
                child_key = self._key(child, polarity)
                if child_key[0] == tag:
                    parts.update(child_key[1])
                else:
                    parts.add(child_key)
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
        self.clauses = {}        # entry id -> (proof node, literal expressions)
        self.by_key = {}         # frozenset of literal keys -> [entry ids]
        self.occurrences = {}    # atom id -> set of entry ids
        self.units = {}          # atom id -> entry id of a unit clause
        self.empty = set()       # entry ids of empty clauses
        self.next_entry = 0
        self.root = None
        self.asserted = self.dag.rule(z3.Z3_OP_PR_ASSERTED, "asserted", 0)
        self.hypothesis = self.dag.rule(z3.Z3_OP_PR_HYPOTHESIS, "hypothesis", 0)
        self.lemma = self.dag.rule(z3.Z3_OP_PR_LEMMA, "lemma", 1)
        self.mp = self.dag.rule(z3.Z3_OP_PR_MODUS_PONENS, "mp", 2)
        self.rewrite = self.dag.rule(z3.Z3_OP_PR_REWRITE, "rewrite", 0)
        self.and_elim = self.dag.rule(z3.Z3_OP_PR_AND_ELIM, "and-elim", 1)
        self.def_axiom = self.dag.rule(z3.Z3_OP_PR_DEF_AXIOM, "def-axiom", 0)
        self.gates = {}          # atom id -> atom, kept alive because z3 reuses identifiers
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
            for clause in clauses:
                node = self.dag.node(self.def_axiom, [self.dag.expression(self.clause_formula(clause))])
                self.add_clause(node, clause)

    # -- clause database -------------------------------------------------

    def clause_formula(self, literals):
        if not literals:
            return z3.BoolVal(False, self.context)
        if len(literals) == 1:
            return literals[0]
        return z3.Or(*literals)

    def add_clause(self, node, literals):
        entry = self.next_entry
        self.next_entry += 1
        self.alive.extend(literals)
        self.clauses[entry] = (node, literals)
        keys = frozenset(_key(literal) for literal in literals)
        self.by_key.setdefault(keys, []).append(entry)
        for atom, _ in keys:
            self.occurrences.setdefault(atom, set()).add(entry)
        if len(keys) == 1 and len(literals) == 1:
            self.units.setdefault(next(iter(keys))[0], entry)
        if not literals:
            self.empty.add(entry)
        return entry

    def delete_clause(self, literals):
        keys = frozenset(_key(literal) for literal in literals)
        entries = self.by_key.get(keys)
        if not entries:
            return  # Deleting an absent clause does not affect soundness.
        entry = entries.pop()
        _, stored = self.clauses.pop(entry)
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
        target = self.normalizer.key(formula)
        for assertion in self.assertions:
            if assertion.get_id() == formula.get_id():
                return self.dag.node(self.asserted, [self.dag.expression(assertion)])
        for assertion in self.assertions:
            for conjunct, path in _conjuncts(assertion):
                if self.normalizer.key(conjunct) == target:
                    return self._derive_assumption(assertion, path, conjunct, formula)
        for assertion in self.assertions:
            for conjunct, path in _conjuncts(assertion):
                if self._valid(conjunct == formula):
                    return self._derive_assumption(assertion, path, conjunct, formula)
        for assertion in self.assertions:
            for conjunct, path in _conjuncts(assertion):
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

    def infer(self, literals, hint):
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
            return self.rup(literals)
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
        if {_key(literal) for literal in lemma_literals} == {_key(literal) for literal in literals}:
            return lemma, lemma_literals
        entry = self.add_clause(lemma, lemma_literals)
        try:
            return self.rup(literals)
        finally:
            self.delete_clause(self.clauses[entry][1]) if entry in self.clauses else None

    def rup(self, literals):
        """Derive a clause by unit propagation, as hypotheses, resolutions, and a lemma."""
        assigned = {}  # atom id -> (polarity, proof node)
        queue = []

        def assign(atom, polarity, node):
            assigned[atom] = (polarity, node)
            queue.append(atom)

        conflict = None
        if self.empty:
            conflict = self.clauses[min(self.empty)][0]
        for literal in literals:
            if conflict is not None:
                break
            complement = _complement(literal)
            atom, polarity = _key(complement)
            node = self.dag.node(self.hypothesis, [self.dag.expression(complement)])
            if atom in assigned:
                if assigned[atom][0] != polarity:
                    # The clause contains complementary literals.
                    conflict = self._resolve(node, [assigned[atom][1]], [complement], [])
                    break
                continue
            assign(atom, polarity, node)
        for atom, entry in list(self.units.items()):
            if conflict is not None:
                break
            node, stored = self.clauses[entry]
            polarity = _key(stored[0])[1]
            if atom not in assigned:
                assign(atom, polarity, node)
            elif assigned[atom][0] != polarity:
                conflict = self._resolve(node, [assigned[atom][1]], stored, [])
        while conflict is None and queue:
            atom = queue.pop()
            for entry in list(self.occurrences.get(atom, ())):
                node, stored = self.clauses[entry]
                false_nodes, open_literal, open_key = [], None, None
                for literal in stored:
                    key = _key(literal)
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
                self.add_clause(node, literals)
            elif head == "infer":
                if len(command) < 2:
                    raise ProofExportError("malformed inference in the clause log")
                hint = terms.hint(command[-1])
                literals = [terms.build(part) for part in command[1:-1]]
                for literal in literals + ([pair[1] for pair in hint[1]] if hint else []):
                    self.ensure_gates(literal)
                node, stored = self.infer(literals, hint)
                if not literals:
                    self.root = node
                self.add_clause(node, stored)
            elif head == "del":
                self.delete_clause([terms.build(part) for part in command[1:]])
            elif head in ("proofs", "set-option", "set-info", "set-logic"):
                continue
            else:
                raise ProofExportError("unsupported clause log command: %s" % head)
        if self.root is None:
            # A contradiction found while asserting or during preprocessing is not
            # logged as an inference, and the log may even be empty. Derive the
            # empty clause by propagation, or tie it to the assertions directly.
            try:
                self.root, _ = self.rup([])
            except ProofExportError:
                self.root = self.assume([])
        return self.dag.certificate(self.source, self.fragment, self.assertion_nodes, self.root)


def build_certificate(source, fragment, assertions, text, context):
    """Rebuild a clause log as an unverified z3-native-proof-dag bundle."""
    return _Replay(source, fragment, assertions, context).run(text)
