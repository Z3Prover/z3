#!/usr/bin/env python3
"""Replay native lp-* arithmetic proof nodes using exact Python arithmetic.

Z3 is used only to access proof ASTs (and, in the command-line driver, produce a
proof). The checker does not call a solver, simplifier, or the LP evidence checker.
Other native proof rules are reported, not certified by this arithmetic checker.
"""

import argparse
from collections import Counter
from dataclasses import dataclass, field
from fractions import Fraction as Q
from math import ceil, floor, gcd, lcm

import z3
from z3.z3 import _to_expr_ref


NONE = 2**32 - 1
NAMES = (
    "lp-input", "lp-linear", "lp-integer-tighten", "lp-integer-lattice",
    "lp-gomory", "lp-monomial-substitute", "lp-monomial-interval", "lp-discharge",
)
EQ, LE, LT, GE, GT = 0, -2, -1, 2, 1


class InvalidProof(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise InvalidProof(message)


def add(dst, src, scale=Q(1)):
    for variable, coefficient in src.items():
        value = dst.get(variable, Q(0)) + scale * coefficient
        if value:
            dst[variable] = value
        else:
            dst.pop(variable, None)
    return dst


def product(p, q):
    result = {}
    for a, x in p.items():
        for b, y in q.items():
            add(result, {tuple(sorted(a + b)): x * y})
    return result


def expression_poly(term):
    """A ring normal form, treating other numeric expressions as opaque atoms."""
    kind = term.decl().kind() if z3.is_app(term) else None
    args = term.children()
    if kind == z3.Z3_OP_ANUM:
        if z3.is_int_value(term):
            return {(): Q(term.as_long())}
        return {(): Q(term.numerator_as_long(), term.denominator_as_long())}
    if kind == z3.Z3_OP_TO_REAL:
        return expression_poly(args[0])
    if kind == z3.Z3_OP_ADD:
        result = {}
        for arg in args:
            add(result, expression_poly(arg))
        return result
    if kind in (z3.Z3_OP_SUB, z3.Z3_OP_UMINUS):
        result = {}
        for i, arg in enumerate(args):
            add(result, expression_poly(arg), Q(1 if i == 0 and len(args) > 1 else -1))
        return result
    if kind == z3.Z3_OP_MUL:
        result = {(): Q(1)}
        for arg in args:
            result = product(result, expression_poly(arg))
        return result
    if kind == z3.Z3_OP_DIV and len(args) == 2:
        divisor = expression_poly(args[1])
        if divisor.keys() == {()} and divisor[()]:
            return add({}, expression_poly(args[0]), 1 / divisor[()])
    require(term.sort().kind() in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT), "Non-arithmetic variable")
    return {(term.get_id(),): Q(1)}


def formula(term):
    if z3.is_true(term):
        return True
    if z3.is_false(term):
        return False
    negated = False
    while z3.is_not(term):
        negated = not negated
        term = term.arg(0)
    if z3.is_true(term) or z3.is_false(term):
        return z3.is_true(term) != negated
    kind = term.decl().kind()
    require(kind in (z3.Z3_OP_EQ, z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT),
            "Expected arithmetic comparison")
    require(not (kind == z3.Z3_OP_EQ and negated), "Disequality is not an LP fact")
    a, b = term.children()
    p = add(expression_poly(a), expression_poly(b), Q(-1))
    if kind in (z3.Z3_OP_GE, z3.Z3_OP_GT):
        p = add({}, p, Q(-1))
    strict = kind in (z3.Z3_OP_LT, z3.Z3_OP_GT)
    equality = kind == z3.Z3_OP_EQ
    if negated:
        p = add({}, p, Q(-1))
        strict = not strict
    if a.sort().kind() == z3.Z3_INT_SORT:
        scale = lcm(*(c.denominator for c in p.values())) if p else 1
        p = add({}, p, Q(scale))
        if strict:
            add(p, {(): Q(1)})
            strict = False
        divisor = 0
        for mon, coefficient in p.items():
            if mon:
                divisor = gcd(divisor, abs(coefficient.numerator))
        if divisor:
            constant = p.pop((), Q(0))
            if equality and constant % divisor:
                return False
            p = add({}, p, Q(1, divisor))
            add(p, {(): constant / divisor if equality else Q(ceil(constant / divisor))})
    if not any(mon for mon in p):
        constant = p.get((), Q(0))
        return constant == 0 if equality else constant < 0 if strict else constant <= 0
    pivot = next(c for mon, c in sorted(p.items()) if mon)
    scale = 1 / (pivot if equality else abs(pivot))
    p = add({}, p, scale)
    return ("eq" if equality else "lt" if strict else "le", tuple(sorted(p.items())))


@dataclass
class Fact:
    kind: int
    contradiction: bool
    rhs: Q
    epsilon: Q
    lhs: list


@dataclass
class Step:
    kind: int
    fact: Fact
    input: int
    assumption: int
    id: int
    equation: Fact
    pivot: int
    definition: int
    source: int
    divisor: Q
    premises: list
    coefficients: list
    bounds: list


class Reader:
    def __init__(self, parameters):
        self.parameters = parameters
        self.cursor = 0

    def take(self):
        require(self.cursor < len(self.parameters), "Truncated LP certificate")
        result = self.parameters[self.cursor]
        self.cursor += 1
        return result

    def rational(self):
        value = self.take()
        require(isinstance(value, (str, int)) and not isinstance(value, bool), "Expected rational parameter")
        try:
            return Q(value)
        except (ValueError, ZeroDivisionError) as error:
            raise InvalidProof("Invalid rational parameter") from error

    def unsigned(self):
        value = self.rational()
        require(value.denominator == 1 and 0 <= value <= NONE, "Expected unsigned parameter")
        return int(value)

    def count(self):
        value = self.unsigned()
        require(value <= len(self.parameters) - self.cursor, "Invalid certificate length")
        return value

    def fact(self):
        kind, contradiction = self.unsigned() - 2, self.unsigned()
        require(kind in (EQ, LE, LT, GE, GT) and contradiction <= 1, "Invalid fact tag")
        rhs, epsilon = self.rational(), self.rational()
        lhs = [(self.rational(), self.unsigned()) for _ in range(self.count())]
        return Fact(kind, bool(contradiction), rhs, epsilon, lhs)


@dataclass
class Certificate:
    variables: list
    monomials: list
    steps: list
    root: int
    expanded: list = field(default_factory=list)
    normalized: list = field(default_factory=list)

    @classmethod
    def decode(cls, parameters):
        r = Reader(parameters)
        require(r.unsigned() == 1, "Unsupported LP certificate version")
        variables = []
        for _ in range(r.count()):
            term = r.take()
            require(isinstance(term, z3.ExprRef), "Expected variable AST parameter")
            term = _to_expr_ref(term.as_ast(), term.ctx)
            integral = r.unsigned()
            require(integral <= 1, "Invalid variable sort flag")
            definition = [(r.rational(), r.unsigned()) for _ in range(r.count())]
            variables.append((term, bool(integral), definition))
        monomials = []
        for _ in range(r.count()):
            column = r.unsigned()
            monomials.append((column, [r.unsigned() for _ in range(r.count())]))
        steps = []
        for _ in range(r.count()):
            kind, fact = r.unsigned(), r.fact()
            ci, assumption, id_ = r.unsigned(), r.unsigned(), r.unsigned()
            equation = r.fact()
            pivot, definition, source = r.unsigned(), r.unsigned(), r.unsigned()
            divisor = r.rational()
            premises, coefficients = [], []
            for _ in range(r.count()):
                premises.append(r.unsigned())
                coefficients.append(r.rational())
            bounds = [(r.unsigned(), r.unsigned(), r.unsigned()) for _ in range(r.count())]
            steps.append(Step(kind, fact, ci, assumption, id_, equation, pivot,
                              definition, source, divisor, premises, coefficients, bounds))
        root = r.unsigned()
        require(r.cursor == len(parameters), "Trailing LP certificate parameters")
        result = cls(variables, monomials, steps, root)
        result.check()
        return result

    def linear(self, terms, expanded=None):
        expanded = self.expanded if expanded is None else expanded
        result = {}
        for c, j in terms:
            require(j < len(expanded), "Invalid variable reference")
            add(result, expanded[j], c)
        return result

    def normalize(self, f):
        require(not f.epsilon and f.kind in (EQ, LE, LT, GE, GT), "Invalid LP fact")
        sign = Q(-1 if f.kind in (GE, GT) else 1)
        return add({}, self.linear(f.lhs), sign), -sign * f.rhs

    def bound(self, s, index, column, lower):
        require(index < len(s.premises) and s.coefficients[index] == 1, "Invalid bound premise")
        f = self.steps[s.premises[index]].fact
        require(not f.contradiction and
                (f.kind == EQ or f.kind in ((GE, GT) if lower else (LE, LT))), "Wrong bound direction")
        p, _ = self.normalize(f)
        require(p == add({}, self.expanded[column], Q(-1 if lower and f.kind != EQ else 1)),
                "Wrong bound variable")
        return f.rhs, f.kind in (LT, GT)

    def identity(self, s, pivot_coefficient):
        require(not s.equation.contradiction and s.equation.kind == EQ and
                self.normalize(s.equation) == ({}, Q(0)), "Invalid tableau identity")
        require(s.pivot < len(self.variables), "Invalid pivot")
        row = {}
        for c, j in s.equation.lhs:
            row[j] = row.get(j, Q(0)) + c
        require(row.get(s.pivot, Q(0)) == pivot_coefficient, "Wrong pivot coefficient")
        return row

    def lattice(self, s, p):
        require(not s.fact.contradiction and s.fact.kind in (LE, GE) and s.divisor > 0,
                "Invalid lattice cut")
        row = self.identity(s, Q(-1))
        upper = s.fact.kind == LE
        fixed, source = {}, None
        for j, lo, hi in s.bounds:
            require(j in row, "Foreign lattice bound")
            if j == s.pivot:
                require(source is None, "Duplicate lattice source")
                source = self.bound(s, hi if upper else lo, j, not upper)
            else:
                lower, lower_open = self.bound(s, lo, j, True)
                higher, higher_open = self.bound(s, hi, j, False)
                require(j not in fixed and lower == higher and not lower_open and not higher_open,
                        "Non-fixed lattice variable")
                fixed[j] = lower
        require(source is not None, "Missing lattice source")
        constant, integral = Q(0), {}
        for j, c in row.items():
            if j != s.pivot:
                if j in fixed:
                    constant += c * fixed[j]
                else:
                    add(integral, self.expanded[j], c / s.divisor)
        require(all(c.denominator == 1 and self.variables[j][1] for j, c in integral.items()),
                "Non-integral lattice")
        value, open_ = source
        q = (value - constant) / s.divisor
        rounded = (ceil(q) - 1 if open_ else floor(q)) if upper else (floor(q) + 1 if open_ else ceil(q))
        require(p == add({}, self.expanded[s.pivot], Q(1 if upper else -1)) and
                s.fact.rhs == s.divisor * rounded + constant, "Wrong lattice rounding")

    def gomory(self, s, normalized):
        require(not s.fact.contradiction and s.fact.kind == GE and self.variables[s.pivot][1],
                "Invalid Gomory conclusion")
        row = self.identity(s, Q(1))
        bounds = {}
        for j, lo, hi in s.bounds:
            require(j != s.pivot and j in row and j not in bounds, "Invalid Gomory bound")
            bounds[j] = lo, hi
        offset, shifted = Q(0), []
        for j, c in row.items():
            if j == s.pivot or not c:
                continue
            lo, hi = bounds.get(j, (NONE, NONE))
            lower = self.bound(s, lo, j, True)[0] if lo != NONE else None
            upper = self.bound(s, hi, j, False)[0] if hi != NONE else None
            if lower is not None and upper is not None:
                require(lower == upper, "Non-fixed Gomory bound")
                offset -= c * lower
                continue
            if self.variables[j][1] and c.denominator == 1:
                continue
            require(lower is not None or upper is not None, "Missing Gomory bound")
            shift = lower if lower is not None else upper
            require(not self.variables[j][1] or shift.denominator == 1, "Fractional integer shift")
            offset -= c * shift
            shifted.append((j, c, shift, lower is not None))
        fraction = offset - floor(offset)
        require(0 < fraction < 1, "Integral Gomory offset")
        lhs, rhs = [], Q(1)
        for j, c, shift, lower in shifted:
            direction = -c if lower else c
            if self.variables[j][1]:
                part = direction - floor(direction)
                weight = min(part / (1 - fraction), (1 - part) / fraction)
            else:
                weight = direction / (1 - fraction) if direction > 0 else -direction / fraction
            weight = weight if lower else -weight
            lhs.append((weight, j))
            rhs += weight * shift
        require(self.normalize(Fact(GE, False, rhs, Q(0), lhs)) == normalized, "Wrong Gomory cut")

    def monomial(self, s, normalized):
        require(not s.fact.contradiction and s.definition < len(self.monomials), "Invalid monomial rule")
        column, factors = self.monomials[s.definition]
        require(column < len(self.variables) and s.pivot < len(self.variables), "Invalid monomial variable")
        require(all(j < len(self.variables) for j in factors), "Invalid monomial factor")
        powers = Counter(factors)
        source = column if s.source == NONE else s.source
        multiplier, shift = Q(1), Q(0)
        if s.source != NONE:
            require(s.kind == 6 and source < len(self.variables) and len(powers) == 2 and
                    len(factors) == 2 and s.pivot in powers and source != column and source not in powers,
                    "Invalid affine monomial source")
            row = self.identity_equation(s)
            other = next(j for j in factors if j != s.pivot)
            require(all(not c or j in (source, column, other) for j, c in row.items()),
                    "Foreign affine source variable")
            multiplier, shift = -row.get(column, Q(0)), -row.get(other, Q(0))
            require(row.get(source) == 1 and multiplier, "Invalid affine source identity")
        boxes = {}
        for j, lo, hi in s.bounds:
            require(j in (column, source) or j in powers, "Foreign monomial bound")
            require(j not in boxes, "Duplicate monomial bound")
            lower = self.bound(s, lo, j, True) if lo != NONE else (None, True)
            upper = self.bound(s, hi, j, False) if hi != NONE else (None, True)
            require(lower[0] is None or upper[0] is None or lower[0] < upper[0] or
                    (lower[0] == upper[0] and not lower[1] and not upper[1]), "Empty monomial interval")
            boxes[j] = Interval(lower[0], upper[0], lower[1], upper[1])
        fixed, unknowns, unknown = Q(1), 0, NONE
        for j, power in powers.items():
            b = boxes.get(j, Interval())
            if b.lo is not None and b.lo == b.hi:
                fixed *= b.lo**power
            else:
                unknowns += power
                unknown = j
        if s.kind == 5:
            require(s.fact.kind == EQ and (unknowns <= 1 or not fixed), "Invalid monomial substitution")
            lhs, rhs = [(Q(1), column)], Q(0)
            if unknowns and fixed:
                lhs.append((-fixed, unknown))
            else:
                rhs = fixed
            require(self.normalize(Fact(EQ, False, rhs, Q(0), lhs)) == normalized,
                    "Wrong monomial substitution")
            return
        upper = s.fact.kind in (LE, LT)
        require(s.fact.kind in (LE, LT, GE, GT), "Invalid interval conclusion")
        require(normalized[0] == add({}, self.expanded[s.pivot], Q(1 if upper else -1)),
                "Wrong interval target")
        upward = s.pivot == column
        require(upward or s.pivot in powers, "Invalid downward target")
        interval = Interval(Q(1), Q(1))
        for j, power in powers.items():
            if upward or j != s.pivot:
                interval = interval.multiply(boxes.get(j, Interval()).power(power))
        exponent = 1
        if not upward:
            positive = interval.lo is not None and (interval.lo > 0 or interval.lo == 0 and interval.lo_open)
            negative = interval.hi is not None and (interval.hi < 0 or interval.hi == 0 and interval.hi_open)
            require(positive or negative, "Division interval contains zero")
            inverse = Interval(None if interval.hi == 0 else Q(0) if interval.hi is None else 1 / interval.hi,
                               None if interval.lo == 0 else Q(0) if interval.lo is None else 1 / interval.lo,
                               interval.hi is None or interval.hi_open,
                               interval.lo is None or interval.lo_open)
            interval = boxes.get(source, Interval()).multiply(inverse)
            if s.source != NONE:
                interval = Interval(None if interval.lo is None else interval.lo - shift,
                                    None if interval.hi is None else interval.hi - shift,
                                    interval.lo_open, interval.hi_open).multiply(
                                        Interval(1 / multiplier, 1 / multiplier))
            exponent = powers[s.pivot]
        value = s.fact.rhs**exponent
        strict = s.fact.kind in (LT, GT)
        above = interval.hi is not None and (value > interval.hi or
                value == interval.hi and (not strict or interval.hi_open))
        below = interval.lo is not None and (value < interval.lo or
                value == interval.lo and (not strict or interval.lo_open))
        if exponent % 2:
            valid = above if upper else below
        else:
            target = boxes.get(s.pivot, Interval())
            if upper:
                valid = above if s.fact.rhs >= 0 else target.hi is not None and target.hi <= 0 and below
            else:
                valid = above if s.fact.rhs <= 0 else target.lo is not None and target.lo >= 0 and below
        require(valid, "Wrong interval conclusion")

    def identity_equation(self, s):
        require(not s.equation.contradiction and s.equation.kind == EQ and
                self.normalize(s.equation) == ({}, Q(0)), "Invalid affine identity")
        row = {}
        for c, j in s.equation.lhs:
            row[j] = row.get(j, Q(0)) + c
        return row

    def check(self):
        require(self.root < len(self.steps), "Invalid LP root")
        self.expanded, self.normalized = [], []
        for i, (term, integral, definition) in enumerate(self.variables):
            require(term.sort().kind() == (z3.Z3_INT_SORT if integral else z3.Z3_REAL_SORT),
                    "Variable sort mismatch")
            require(all(j < i and (not integral or c.denominator == 1 and self.variables[j][1])
                        for c, j in definition), "Invalid variable definition")
            self.expanded.append(self.linear(definition) if definition else {i: Q(1)})
            if definition:
                actual = {}
                for c, j in definition:
                    add(actual, expression_poly(self.variables[j][0]), c)
                require(not add(actual, expression_poly(term), Q(-1)), "Native definition mismatch")
        for i, s in enumerate(self.steps):
            require(0 <= s.kind < len(NAMES) and (s.kind == 7 or s.assumption == NONE), "Invalid LP rule")
            require(len(s.premises) == len(s.coefficients) and all(j < i for j in s.premises),
                    "Invalid premise reference")
            require(all(j < len(self.variables) and
                        (lo == NONE or lo < len(s.premises)) and
                        (hi == NONE or hi < len(s.premises)) for j, lo, hi in s.bounds),
                    "Invalid column bound reference")
            normalized = self.normalize(s.fact)
            p, constant = normalized
            if s.kind == 0:
                require(s.input != NONE and not s.fact.contradiction and not s.premises, "Invalid LP input")
            elif s.kind == 1:
                result, total, strict, equality = {}, Q(0), False, True
                for j, c in zip(s.premises, s.coefficients):
                    f = self.steps[j].fact
                    require(not f.contradiction and (f.kind == EQ or c >= 0), "Invalid linear coefficient")
                    q, k = self.normalized[j]
                    add(result, q, c)
                    total += c * k
                    if c:
                        strict |= f.kind in (LT, GT)
                        equality &= f.kind == EQ
                if s.fact.contradiction:
                    require(not result and (total > 0 or strict and total == 0 or equality and total != 0),
                            "Non-contradictory linear sum")
                else:
                    require(result == p, "Wrong linear polynomial")
                    slack = total - constant
                    require(equality and slack == 0 if s.fact.kind == EQ else
                            slack >= 0 and not (s.fact.kind in (LT, GT) and not strict and slack == 0),
                            "Wrong linear bound")
            elif s.kind == 2:
                require(not s.fact.contradiction and len(s.premises) == 1 and s.coefficients == [Q(1)],
                        "Invalid integer tightening")
                j = s.premises[0]
                f = self.steps[j].fact
                require(not f.contradiction and self.normalized[j][0] == p and not f.epsilon and
                        all(c.denominator == 1 and self.variables[k][1] for k, c in p.items()),
                        "Non-integral tightening")
                if f.kind in (LE, LT) and s.fact.kind == LE:
                    value = ceil(f.rhs) - 1 if f.kind == LT else floor(f.rhs)
                elif f.kind in (GE, GT) and s.fact.kind == GE:
                    value = floor(f.rhs) + 1 if f.kind == GT else ceil(f.rhs)
                else:
                    raise InvalidProof("Wrong integer tightening direction")
                require(s.fact.rhs == value, "Wrong integer rounding")
            elif s.kind == 3:
                self.lattice(s, p)
            elif s.kind == 4:
                require(s.pivot < len(self.variables), "Invalid Gomory pivot")
                self.gomory(s, normalized)
            elif s.kind in (5, 6):
                self.monomial(s, normalized)
                column, factors = self.monomials[s.definition]
                actual = {(): Q(1)}
                for j in factors:
                    actual = product(actual, expression_poly(self.variables[j][0]))
                require(not add(actual, expression_poly(self.variables[column][0]), Q(-1)),
                        "Native monomial definition mismatch")
            else:
                require(not s.fact.contradiction and len(s.premises) == 1 and s.coefficients == [Q(1)] and
                        self.steps[s.premises[0]].fact.contradiction and s.assumption < i and
                        self.steps[s.assumption].kind == 0, "Invalid assumption discharge")
                f = self.steps[s.assumption].fact
                q, k = self.normalized[s.assumption]
                require({LT: GE, LE: GT, GT: LE, GE: LT}.get(f.kind) == s.fact.kind and
                        p == add({}, q, Q(-1)) and constant == -k, "Wrong discharged bound")
            self.normalized.append(normalized)

    def expression(self, f):
        ctx = self.variables[0][0].ctx if self.variables else None
        if f.contradiction:
            return z3.BoolVal(False, ctx)
        integral = all(self.variables[j][1] for _, j in f.lhs)
        # Build only the expected expression; formula() performs independent ring
        # normalization and integer-lattice normalization, without Z3 rewriting.
        scale = lcm(f.rhs.denominator, *(c.denominator for c, _ in f.lhs)) if integral else 1
        zero = z3.IntVal(0, ctx) if integral else z3.RealVal(0, ctx)
        lhs = zero
        for c, j in f.lhs:
            term = self.variables[j][0]
            if not integral and term.sort().kind() == z3.Z3_INT_SORT:
                term = z3.ToReal(term)
            coefficient = z3.IntVal(int(scale * c), ctx) if integral else z3.RealVal(str(c), ctx)
            lhs = lhs + coefficient * term
        rhs = z3.IntVal(int(scale * f.rhs), ctx) if integral else z3.RealVal(str(f.rhs), ctx)
        expressions = {EQ: lambda: lhs == rhs, LE: lambda: lhs <= rhs, LT: lambda: lhs < rhs,
                       GE: lambda: lhs >= rhs, GT: lambda: lhs > rhs}
        return expressions[f.kind]()

    def native_fact(self, f):
        return formula(self.expression(f))


@dataclass
class Interval:
    lo: object = None
    hi: object = None
    lo_open: bool = False
    hi_open: bool = False

    def contains_zero(self):
        return (self.lo is None or self.lo < 0 or self.lo == 0 and not self.lo_open) and (
            self.hi is None or self.hi > 0 or self.hi == 0 and not self.hi_open)

    def multiply(self, other):
        endpoints = []
        zero = self.contains_zero() or other.contains_zero()
        for x, xi, xo in ((self.lo, -1, self.lo_open), (self.hi, 1, self.hi_open)):
            for y, yi, yo in ((other.lo, -1, other.lo_open), (other.hi, 1, other.hi_open)):
                if x == 0 or y == 0:
                    endpoints.append(((0, Q(0)), not zero))
                elif x is None or y is None:
                    xs = xi if x is None else 1 if x > 0 else -1
                    ys = yi if y is None else 1 if y > 0 else -1
                    endpoints.append(((xs * ys, Q(0)), True))
                else:
                    endpoints.append(((0, x * y), xo or yo))
        lo, hi = min(x for x, _ in endpoints), max(x for x, _ in endpoints)
        return Interval(None if lo[0] else lo[1], None if hi[0] else hi[1],
                        all(open_ for x, open_ in endpoints if x == lo),
                        all(open_ for x, open_ in endpoints if x == hi))

    def power(self, exponent):
        lo = None if self.lo is None else self.lo**exponent
        hi = None if self.hi is None else self.hi**exponent
        if exponent % 2:
            return Interval(lo, hi, self.lo_open, self.hi_open)
        upper = None if lo is None or hi is None else max(lo, hi)
        upper_open = (lo != upper or self.lo_open) and (hi != upper or self.hi_open)
        if self.lo is not None and self.lo > 0:
            return Interval(lo, upper, self.lo_open, upper_open)
        if self.hi is not None and self.hi < 0:
            return Interval(hi, upper, self.hi_open, upper_open)
        return Interval(Q(0), upper, not self.contains_zero(), upper_open)


def check_lp_nodes(proof):
    """Return counts of checked LP nodes and unexamined non-LP native nodes."""
    contexts, seen, counts = {}, set(), Counter()
    todo = [proof]
    while todo:
        node = todo.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        children = node.children()
        require(children, "Proof node without a conclusion")
        parents, conclusion = children[:-1], children[-1]
        require(all(parent.sort().eq(node.sort()) for parent in parents), "Non-proof premise")
        todo.extend(parents)
        ps = node.decl().params()
        lp_rule = (node.decl().kind() == z3.Z3_OP_PR_TH_LEMMA and len(ps) >= 2 and
                   ps[0] == "arith" and isinstance(ps[1], str) and ps[1].startswith("lp-"))
        if not lp_rule:
            counts["other"] += 1
            continue
        tag = ps[1]
        context = node if tag == "lp-context" else parents[0] if parents else None
        require(context is not None, "Missing LP context")
        if context.get_id() not in contexts:
            context_ps = context.decl().params()
            require(context.decl().kind() == z3.Z3_OP_PR_TH_LEMMA and
                    context_ps[:2] == ["arith", "lp-context"] and
                    context.num_args() == 1 and z3.is_true(context.arg(0)), "Malformed LP context")
            contexts[context.get_id()] = Certificate.decode(context_ps[2:])
        cert = contexts[context.get_id()]
        if tag == "lp-context":
            counts[tag] += 1
            continue
        require(len(ps) >= 3, "Invalid LP inference parameters")
        r = Reader(ps[2:])
        index = r.unsigned()
        require(index < len(cert.steps), "Invalid LP step index")
        s = cert.steps[index]
        def scale(f):
            return (lcm(f.rhs.denominator, *(c.denominator for c, _ in f.lhs))
                    if not f.contradiction and all(cert.variables[j][1] for _, j in f.lhs) else 1)

        weights = []
        if s.kind == 1:
            weights = [c / scale(cert.steps[j].fact) for c, j in zip(s.coefficients, s.premises)]
            if not s.fact.contradiction:
                weights.append(Q(1, scale(s.fact)))
        require(len(ps) == 3 + len(weights) and [Q(c) for c in ps[3:]] == weights,
                "Wrong local linear coefficients")
        require(tag == NAMES[s.kind] and formula(conclusion) == cert.native_fact(s.fact),
                "Wrong native LP conclusion")
        if s.kind == 0:
            require(len(parents) in (1, 2), "Invalid native LP input arity")
            actual = True if len(parents) == 1 else formula(parents[1].arg(parents[1].num_args() - 1))
            require(actual == cert.native_fact(s.fact), "Wrong native LP input")
        elif s.kind == 7:
            require(len(parents) == 2 and parents[1].decl().kind() == z3.Z3_OP_PR_LEMMA and
                    parents[1].num_args() == 2, "Missing native discharge lemma")
            lemma = parents[1]
            require(z3.is_false(lemma.arg(0).arg(lemma.arg(0).num_args() - 1)),
                    "Discharge body is not a contradiction")
            negation = z3.Not(cert.expression(cert.steps[s.assumption].fact))
            require(formula(lemma.arg(1)) == formula(negation), "Wrong native discharge assumption")
        else:
            require(len(parents) == len(s.premises) + 1, "Wrong native LP premise count")
            for parent, j in zip(parents[1:], s.premises):
                require(formula(parent.arg(parent.num_args() - 1)) == cert.native_fact(cert.steps[j].fact),
                        "Wrong native LP premise")
        counts[tag] += 1
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", help="SMT-LIB2 input used to produce a native proof")
    args = parser.parse_args()
    ctx = z3.Context(proof=True)
    solver = z3.Solver(ctx=ctx)
    solver.set("arith.solver", 6)
    solver.from_file(args.file)
    require(solver.check() == z3.unsat, "Input did not produce an UNSAT proof")
    counts = check_lp_nodes(solver.proof())
    checked = sum(count for tag, count in counts.items() if tag != "other")
    require(checked > 0, "No native LP certificate was emitted")
    print(f"Checked {checked} LP proof nodes; {counts['other']} non-LP nodes were not checked.")


if __name__ == "__main__":
    main()
