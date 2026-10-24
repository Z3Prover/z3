#!/usr/bin/env python3
"""Independent bounded checker and experimental Alethe FF-extension exporter.

Uses Python integer arithmetic only: no Z3, computer algebra, or solver library.
See doc/QF_FF_CERTIFICATES.md for scope and the ff-poly-v1 rule contract.
"""
import argparse
from pathlib import Path
import re
import sys
import time


class Invalid(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Invalid(message)


def natural(x):
    require(isinstance(x, str) and re.fullmatch(r"0|[1-9][0-9]*", x), "expected canonical natural number")
    require(len(x) <= 1300, "integer resource limit")
    return int(x)


def symbol(x):
    require(isinstance(x, str) and x and not x.startswith('"'), "expected symbol")
    return x[1:-1] if x.startswith('|') and x.endswith('|') else x


def parse(text, max_depth=200):
    require(len(text) <= 32 * 1024 * 1024, "file size limit")
    # Preserve quoted symbols and strings, including SMT-LIB doubled quotes.
    token = re.compile(r'\s+|;[^\n]*|\(|\)|\|[^|\\]*\||"(?:[^"]|"")*"|[^\s();|"\\]+')
    root, stack, pos, count = [], [], 0, 0
    stack.append(root)
    while pos < len(text):
        match = token.match(text, pos)
        require(match is not None, "invalid S-expression token")
        t = match.group(); pos = match.end()
        if t.isspace() or t.startswith(';'):
            continue
        count += 1
        require(count <= 2000000, "token limit")
        if t == '(':
            child = []; stack[-1].append(child); stack.append(child)
            require(len(stack) <= max_depth, "nesting limit")
        elif t == ')':
            require(len(stack) > 1, "unbalanced parentheses")
            stack.pop()
        else:
            stack[-1].append(t)
    require(len(stack) == 1, "unclosed parentheses")
    return root


def sexpr(x):
    return '(' + ' '.join(map(sexpr, x)) + ')' if isinstance(x, list) else x


def attributes(xs, allowed):
    require(len(xs) % 2 == 0, "malformed attributes")
    result = {}
    for key, value in zip(xs[::2], xs[1::2]):
        require(isinstance(key, str) and key in allowed and key not in result, "unknown/duplicate attribute")
        result[key] = value
    require(set(result) == set(allowed), "missing attribute")
    return result


class Arithmetic:
    def __init__(self, prime):
        require(2 <= prime and prime.bit_length() <= 4096, "modulus out of range")
        self.p = prime
        self.work = 0
        self.retained = 0

    def tick(self, n=1):
        self.work += n
        require(self.work <= 20000000, "checker work limit")

    def keep(self, value):
        self.retained += sum(1 + len(mon) for mon in value)
        require(self.retained <= 2000000, "checker retained-term limit")
        return value

    def release(self, value):
        self.retained -= sum(1 + len(mon) for mon in value)

    def add(self, a, b, scale=1):
        self.tick(len(a) + len(b))
        out = a.copy()
        for mon, c in b.items():
            value = (out.get(mon, 0) + scale * c) % self.p
            if value:
                out[mon] = value
            else:
                out.pop(mon, None)
        require(len(out) <= 100000, "checker polynomial limit")
        return out

    def mul(self, a, b):
        out = {}
        for ma, ca in a.items():
            for mb, cb in b.items():
                self.tick(1 + len(ma) + len(mb))
                require(len(ma) + len(mb) <= 1024, "checker degree limit")
                mon = tuple(sorted(ma + mb))
                value = (out.get(mon, 0) + ca * cb) % self.p
                if value:
                    out[mon] = value
                else:
                    out.pop(mon, None)
                require(len(out) <= 100000, "checker polynomial limit")
        return out


class Problem:
    """Strict, single-context SMT-LIB subset; unsupported commands fail closed."""
    def __init__(self, text):
        self.sorts, self.declarations, self.definitions = {}, {}, {}
        self.assertions, self.equations, self.origins = [], [], []
        self.walk_work = 0
        for cmd in parse(text):
            require(isinstance(cmd, list) and cmd, "expected SMT-LIB command")
            op = cmd[0]
            if op in ('set-logic', 'set-option', 'set-info', 'check-sat', 'get-info', 'get-model', 'get-proof', 'get-statistics', 'ff-certify', 'exit'):
                continue
            if op == 'define-sort':
                require(len(cmd) == 4 and cmd[2] == [], "only nullary sort aliases supported")
                name = symbol(cmd[1]); require(name not in self.sorts, "duplicate sort")
                self.sorts[name] = self.sort(cmd[3])
            elif op in ('declare-const', 'declare-fun'):
                require((op == 'declare-const' and len(cmd) == 3) or
                        (op == 'declare-fun' and len(cmd) == 4 and cmd[2] == []), "only field constants supported")
                name = symbol(cmd[1]); require(name not in self.declarations and name not in self.definitions, "duplicate declaration")
                self.declarations[name] = (cmd[1], self.sort(cmd[-1]))
            elif op == 'define-fun':
                require(len(cmd) == 5 and cmd[2] == [], "only nullary definitions supported")
                name = symbol(cmd[1]); require(name not in self.declarations and name not in self.definitions, "duplicate definition")
                # Expand earlier definitions now; reject recursive definitions
                # and sort mistakes during normalization, without trusting Z3.
                value = self.expand(cmd[4])
                self.check_symbols(value)
                self.definitions[name] = (self.sort(cmd[3]), value)
            elif op == 'assert':
                require(len(cmd) == 2, "malformed assertion")
                expanded = self.expand(cmd[1])
                # Require declarations to precede assertions, including names
                # that would otherwise acquire a meaning later in the file.
                self.check_symbols(expanded)
                index = len(self.assertions)
                self.assertions.append(cmd[1])
                for leaf, eq in enumerate(self.flatten(expanded)):
                    require(isinstance(eq, list) and len(eq) == 3 and eq[0] == '=', "only conjunctions of field equalities supported")
                    require(len(self.equations) < 4096, "equation limit")
                    self.equations.append(eq)
                    self.origins.append((index, leaf))
            else:
                raise Invalid(f"unsupported SMT-LIB command: {op}")
        require(self.equations, "no field equations")

    def tick(self):
        self.walk_work += 1
        require(self.walk_work <= 2000000, "problem expansion limit")

    def sort(self, s):
        if isinstance(s, str):
            require(symbol(s) in self.sorts, "unknown field sort")
            return self.sorts[symbol(s)]
        require(len(s) == 3 and s[:2] == ['_', 'FiniteField'], "expected prime field sort")
        p = natural(s[2]); require(p >= 2 and p.bit_length() <= 4096, "invalid modulus")
        return p

    def expand(self, e, local=None):
        self.tick()
        local = {} if local is None else local
        if isinstance(e, str):
            name = symbol(e)
            if name in local:
                return local[name]
            if name in self.definitions:
                p, value = self.definitions[name]
                return ['as', value, ['_', 'FiniteField', str(p)]]
            return e
        require(e, "empty term")
        if e[0] == 'let':
            require(len(e) == 3 and isinstance(e[1], list), "malformed let")
            bindings = {}
            for b in e[1]:
                require(isinstance(b, list) and len(b) == 2, "malformed let binding")
                name = symbol(b[0]); require(name not in bindings, "duplicate let binding")
                bindings[name] = self.expand(b[1], local)
            return self.expand(e[2], local | bindings)
        if e[0] == '!':
            require(len(e) >= 4 and len(e) % 2 == 0, "malformed annotation")
            require(all(e[i] == ':named' for i in range(2, len(e), 2)), "unsupported annotation")
            return self.expand(e[1], local)
        if e[0] == '_':
            return e
        if e[0] == 'as':
            require(len(e) == 3, "malformed ascription")
            return ['as', self.expand(e[1], local), e[2]]
        return [e[0]] + [self.expand(x, local) for x in e[1:]]

    def check_symbols(self, e):
        self.tick()
        if isinstance(e, str):
            if re.fullmatch(r'#f-?[0-9]+m[0-9]+', e):
                return
            require(symbol(e) in self.declarations, "undeclared field constant")
        elif e[0] == '_':
            return
        elif e[0] == 'as':
            if not (isinstance(e[1], str) and re.fullmatch(r'ff-?[0-9]+', e[1])):
                self.check_symbols(e[1])
        else:
            for arg in e[1:]:
                self.check_symbols(arg)

    @staticmethod
    def flatten(e):
        if isinstance(e, list) and e and e[0] == 'and':
            for x in e[1:]:
                yield from Problem.flatten(x)
        else:
            yield e

    def term(self, e, names, ar):
        ar.tick()
        if isinstance(e, str):
            short = re.fullmatch(r'#f(-?[0-9]+)m([0-9]+)', e)
            if short:
                return self.term(['as', 'ff' + short[1], ['_', 'FiniteField', short[2]]], names, ar)
            name = symbol(e)
            require(name in names and name in self.declarations, "unknown certificate variable")
            require(self.declarations[name][1] == ar.p, "variable field mismatch")
            return {(names[name],): 1}
        require(isinstance(e, list) and e, "expected field term")
        op = e[0]
        if op == 'as':
            require(len(e) == 3 and self.sort(e[2]) == ar.p, "ascription field mismatch")
            if isinstance(e[1], str) and re.fullmatch(r'ff-?[0-9]+', e[1]):
                require(len(e[1]) <= 1302, "numeral resource limit")
                c = int(e[1][2:]) % ar.p
                return {(): c} if c else {}
            return self.term(e[1], names, ar)
        if op == 'ff.neg':
            require(len(e) == 2, "negation arity")
            return ar.add({}, self.term(e[1], names, ar), -1)
        require(op in ('ff.add', 'ff.mul', 'ff.bitsum') and len(e) >= 3, "unsupported field term")
        result = {(): 1} if op == 'ff.mul' else {}
        for i, arg in enumerate(e[1:]):
            value = self.term(arg, names, ar)
            if op == 'ff.mul':
                result = ar.mul(result, value)
            else:
                result = ar.add(result, value, pow(2, i, ar.p) if op == 'ff.bitsum' else 1)
        return result

    def equation(self, eq, names, ar):
        require(isinstance(eq, list) and len(eq) == 3 and eq[0] == '=', "expected equation")
        return ar.add(self.term(eq[1], names, ar), self.term(eq[2], names, ar), -1)


def decode_polynomial(raw, ar, count):
    require(isinstance(raw, list), "expected polynomial")
    out = {}
    for term in raw:
        require(isinstance(term, list) and term, "expected coefficient and monomial")
        c = natural(term[0]); mon = tuple(map(natural, term[1:]))
        require(0 < c < ar.p and len(mon) <= 1024 and all(v < count for v in mon), "noncanonical term")
        require(tuple(sorted(mon)) == mon and mon not in out, "noncanonical monomial")
        out[mon] = c
    ar.tick(sum(1 + len(mon) for mon in out))
    return out


def balance_certificate(text):
    """Untrusted producer optimization; the returned DAG still requires verify().

    Flatten only single-use add/multiply chains and balance their sums. Shared
    nodes remain anchors, avoiding exponential expansion of global multipliers.
    This changes only ring identities, never the input equations or checker.
    """
    objects = parse(text)
    require(len(objects) == 1 and isinstance(objects[0], list) and objects[0] and objects[0][0] == 'ff-certificate', 'expected certificate')
    c = attributes(objects[0][1:], {':version', ':modulus', ':variables', ':inputs', ':nodes', ':root'})
    require(c[':version'] == '1', 'unsupported certificate version')
    p = natural(c[':modulus']); require(2 <= p and p.bit_length() <= 4096, 'modulus out of range')
    require(isinstance(c[':variables'], list) and isinstance(c[':inputs'], list), 'invalid certificate inputs')
    nodes = c[':nodes']; require(isinstance(nodes, list) and 0 < len(nodes) <= 100000, 'node limit')
    root = natural(c[':root']); require(root < len(nodes), 'bad root')
    parents, factors = [], {}
    for i, n in enumerate(nodes):
        require(isinstance(n, list) and n, 'malformed node')
        if n[0] == 'input':
            require(len(n) == 2 and natural(n[1]) < len(c[':inputs']), 'bad input reference'); ps = []
        elif n[0] == 'add':
            require(len(n) == 3, 'bad addition'); ps = [natural(n[1]), natural(n[2])]
        elif n[0] == 'mul':
            require(len(n) == 4 and isinstance(n[3], list), 'bad multiplication')
            ps = [natural(n[1])]; coefficient = natural(n[2]); mon = tuple(map(natural, n[3]))
            require(0 < coefficient < p and len(mon) <= 1024 and tuple(sorted(mon)) == mon and
                    all(v < len(c[':variables']) for v in mon), 'noncanonical multiplier')
            factors[i] = coefficient, mon
        else: raise Invalid('unknown derivation rule')
        require(all(j < i for j in ps), 'bad derivation reference'); parents.append(ps)
    live, pending, uses = set(), [root], [0]*len(nodes)
    while pending:
        i = pending.pop()
        if i in live: continue
        live.add(i)
        for j in parents[i]: uses[j] += 1; pending.append(j)
    anchors = {i for i in live if uses[i] > 1 or nodes[i][0] == 'input'} | {root}
    renamed, result = {}, []
    work = 0
    def emit(n):
        require(len(result) < 100000, 'balanced DAG node limit')
        result.append(n); return len(result)-1
    for i in sorted(anchors):
        if nodes[i][0] == 'input': renamed[i] = emit(nodes[i]); continue
        terms, pending = {}, [(i, 1, ())]
        while pending:
            j, coefficient, mon = pending.pop()
            work += 1 + len(mon); require(work <= 2000000, 'balance work limit')
            if j != i and j in anchors:
                key = renamed[j], mon
                terms[key] = (terms.get(key, 0) + coefficient) % p
            elif nodes[j][0] == 'add':
                pending.extend((k, coefficient, mon) for k in parents[j])
            else:
                scale, factor = factors[j]
                require(len(mon)+len(factor) <= 1024, 'balance degree limit')
                pending.append((parents[j][0], coefficient*scale % p, tuple(sorted(mon+factor))))
        terms = {k: v for k, v in terms.items() if v}
        summands = []
        for (j, mon), coefficient in sorted(terms.items()):
            summands.append(j if coefficient == 1 and not mon else
                            emit(['mul', str(j), str(coefficient), list(map(str, mon))]))
        if not summands:
            # Produce zero from an existing input, never a new constant axiom.
            j = next(iter(renamed.values())); negative = emit(['mul', str(j), str(p-1), []])
            summands = [emit(['add', str(j), str(negative)])]
        while len(summands) > 1:
            level = []
            for k in range(0, len(summands), 2):
                level.append(summands[k] if k+1 == len(summands) else
                             emit(['add', str(summands[k]), str(summands[k+1])]))
            summands = level
        renamed[i] = summands[0]
    # Do not enlarge an already compact derivation merely to change its shape.
    if len(result) > len(nodes): return text
    c[':nodes'], c[':root'] = result, str(renamed[root])
    out = sexpr(['ff-certificate'] + [x for kv in c.items() for x in kv]) + '\n'
    require(len(out.encode()) <= 32*1024*1024, 'balanced certificate size limit')
    return out


def schedule_certificate(text):
    """Untrusted dependency-first scheduling; preserve every ring operation.

    Balancing can otherwise emit all products of a sum before any addition,
    retaining many large expanded polynomials simultaneously. Visit a subtree
    before its sibling, and emit shared nodes once. Independent replay remains
    mandatory after this purely structural producer transformation.
    """
    c = read_certificate(text)
    nodes, result, renamed = c[':nodes'], [], {}
    pending = [(natural(c[':root']), False)]
    while pending:
        i, ready = pending.pop()
        if i in renamed:
            continue
        node = nodes[i]
        parents = node[1:3] if node[0] == 'add' else node[1:2] if node[0] == 'mul' else []
        if not ready:
            pending.append((i, True))
            pending.extend((natural(j), False) for j in reversed(parents))
            continue
        node = list(node)
        if parents:
            node[1] = str(renamed[natural(node[1])])
        if node[0] == 'add':
            node[2] = str(renamed[natural(node[2])])
        renamed[i] = len(result)
        result.append(node)
    c[':nodes'], c[':root'] = result, str(renamed[natural(c[':root'])])
    return sexpr(['ff-certificate'] + [x for kv in c.items() for x in kv]) + '\n'


def try_balance_certificate(text):
    # Local normalization limits do not invalidate an existing recorded proof.
    # The original or transformed DAG is always checked before it is accepted.
    try: text = balance_certificate(text)
    except Invalid: pass
    try: return schedule_certificate(text)
    except Invalid: return text


def read_certificate(certificate_text):
    """Validate bounded DAG syntax, without claiming an input-bound proof."""
    objects = parse(certificate_text)
    require(len(objects) == 1 and isinstance(objects[0], list) and objects[0] and objects[0][0] == 'ff-certificate', "expected one certificate")
    cert = attributes(objects[0][1:], {':version', ':modulus', ':variables', ':inputs', ':nodes', ':root'})
    require(cert[':version'] == '1', "unsupported certificate version")
    ar = Arithmetic(natural(cert[':modulus']))
    require(isinstance(cert[':variables'], list) and isinstance(cert[':inputs'], list), "invalid certificate inputs")
    nodes = cert[':nodes']
    require(isinstance(nodes, list) and 0 < len(nodes) <= 100000, "node limit")
    require(natural(cert[':root']) < len(nodes), "bad root")
    for i, node in enumerate(nodes):
        require(isinstance(node, list) and node, "malformed node")
        if node[0] == 'input':
            require(len(node) == 2 and natural(node[1]) < len(cert[':inputs']), "bad input reference")
        elif node[0] == 'add':
            require(len(node) == 3 and natural(node[1]) < i and natural(node[2]) < i, "bad addition references")
        elif node[0] == 'mul':
            require(len(node) == 4 and natural(node[1]) < i and isinstance(node[3], list), "bad multiplication")
            decode_polynomial([[node[2]] + node[3]], ar, len(cert[':variables']))
        else:
            raise Invalid("unknown derivation rule")
    return cert


def verify(problem_text, certificate_text):
    return verify_problem(Problem(problem_text), certificate_text)


def verify_problem(problem, certificate_text, *, retain_values=True, on_node=None):
    """Replay a DAG against independently supplied typed input equations.

    Streaming mode releases a value only after its last reference. It applies
    the same storage bound to live values (including normalized inputs), while
    retaining the cumulative arithmetic work bound and checking even dead nodes.
    on_node receives provisional values; callers must discard its output unless
    this function returns successfully with a checked contradiction.
    """
    objects = parse(certificate_text)
    require(len(objects) == 1 and isinstance(objects[0], list) and objects[0] and objects[0][0] == 'ff-certificate', "expected one certificate")
    cert = attributes(objects[0][1:], {':version', ':modulus', ':variables', ':inputs', ':nodes', ':root'})
    require(cert[':version'] == '1', "unsupported certificate version")
    ar = Arithmetic(natural(cert[':modulus']))
    require(isinstance(cert[':variables'], list), "expected variable list")
    names = {}
    for i, name in enumerate(cert[':variables']):
        key = symbol(name)
        require(key not in names and key in problem.declarations and problem.declarations[key][1] == ar.p, "invalid variable declaration")
        names[key] = i
    # Typed DAG frontends may release normalized subterms after their last
    # use. Charge each resulting input immediately so normalization and replay
    # share the same bound on simultaneously retained polynomials.
    normalized = (problem.equation_values(names, ar) if hasattr(problem, 'equation_values')
                  else (problem.equation(eq, names, ar) for eq in problem.equations))
    inputs = [value if retain_values else ar.keep(value) for value in normalized]
    require(isinstance(cert[':inputs'], list) and len(inputs) == len(cert[':inputs']), "input count mismatch")
    for expected, raw in zip(inputs, cert[':inputs']):
        require(expected == decode_polynomial(raw, ar, len(names)), "input normalization mismatch")
    nodes = cert[':nodes']
    require(isinstance(nodes, list) and 0 < len(nodes) <= 100000, "node limit")
    root = natural(cert[':root'])
    require(root < len(nodes), "root does not derive 1 = 0")
    # Validate references before any callback sees the certificate. Count both
    # edges of add(i, i): sharing must never free an operand prematurely.
    references, uses = [], [0] * len(nodes)
    uses[root] = 1
    for i, node in enumerate(nodes):
        require(isinstance(node, list) and node, "malformed node")
        if node[0] == 'input':
            require(len(node) == 2 and natural(node[1]) < len(inputs), "bad input reference")
            parents = ()
        elif node[0] == 'add':
            require(len(node) == 3 and natural(node[1]) < i and natural(node[2]) < i, "bad addition references")
            parents = (natural(node[1]), natural(node[2]))
        elif node[0] == 'mul':
            require(len(node) == 4 and natural(node[1]) < i and isinstance(node[3], list), "bad multiplication")
            parents = (natural(node[1]),)
        else:
            raise Invalid("unknown derivation rule")
        references.append(parents)
        for parent in parents:
            uses[parent] += 1
    values = []
    for i, node in enumerate(nodes):
        parents = references[i]
        if node[0] == 'input':
            value = inputs[natural(node[1])]
        elif node[0] == 'add':
            value = ar.add(values[parents[0]], values[parents[1]])
        else:
            factor = decode_polynomial([[node[2]] + node[3]], ar, len(names))
            value = ar.mul(values[parents[0]], factor)
        values.append(ar.keep(value))
        if on_node is not None:
            on_node(cert, i, value)
        if not retain_values:
            for parent in parents:
                uses[parent] -= 1
                if not uses[parent]:
                    ar.release(values[parent])
                    values[parent] = None
            if not uses[i]:
                ar.release(value)
                values[i] = None
    require(values[root] == {(): 1}, "root does not derive 1 = 0")
    return problem, cert, values if retain_values else None


def polynomial_term(value, p, variables):
    def numeral(c):
        return ['as', 'ff' + str(c), ['_', 'FiniteField', str(p)]]
    terms = []
    for mon, c in sorted(value.items(), reverse=True):
        factors = ([numeral(c)] if c != 1 or not mon else []) + [variables[v] for v in mon]
        terms.append(factors[0] if len(factors) == 1 else ['ff.mul'] + factors)
    return numeral(0) if not terms else terms[0] if len(terms) == 1 else ['ff.add'] + terms


def export_alethe(problem_text, certificate_text):
    problem, cert, values = verify(problem_text, certificate_text)
    p, variables = natural(cert[':modulus']), cert[':variables']
    out = ['; Experimental ff-poly-v1 Alethe extension; custom rules require checker support.']
    for i, assertion in enumerate(problem.assertions):
        out.append(sexpr(['assume', 'a' + str(i), assertion]))
    for i, node in enumerate(cert[':nodes']):
        conclusion = ['cl', ['=', polynomial_term(values[i], p, variables), ['as', 'ff0', ['_', 'FiniteField', str(p)]]]]
        step = ['step', 't' + str(i), conclusion]
        if node[0] == 'input':
            origin, leaf = problem.origins[natural(node[1])]
            step += [':rule', 'ff_poly_input', ':premises', ['a' + str(origin)], ':args', [str(leaf)]]
        elif node[0] == 'add':
            step += [':rule', 'ff_poly_add', ':premises', ['t' + node[1], 't' + node[2]], ':args', []]
        else:
            factor = {tuple(map(natural, node[3])): natural(node[2])}
            step += [':rule', 'ff_poly_mul', ':premises', ['t' + node[1]], ':args', [polynomial_term(factor, p, variables)]]
        out.append(sexpr(step))
    out.append(sexpr(['step', 'contradiction', ['cl'], ':rule', 'ff_poly_contra', ':premises', ['t' + cert[':root']], ':args', []]))
    return '\n'.join(out) + '\n'


def verify_alethe(problem_text, proof_text):
    problem = Problem(problem_text)
    # The field is obtained from the original formula, never the certificate.
    # Try each declared/numeral field to normalize the whole conjunction.
    fields = {p for _, p in problem.declarations.values()}
    def numerals(x):
        if isinstance(x, list):
            if len(x) == 3 and x[0] == 'as':
                fields.add(problem.sort(x[2]))
                numerals(x[1])
            else:
                for a in x: numerals(a)
        elif isinstance(x, str):
            match = re.fullmatch(r'#f-?[0-9]+m([0-9]+)', x)
            if match: fields.add(natural(match[1]))
    numerals(problem.equations)
    valid = []
    names = {name: i for i, name in enumerate(problem.declarations)}
    for p in fields:
        ar = Arithmetic(p)
        try:
            inputs = [problem.equation(eq, names, ar) for eq in problem.equations]
            valid.append((ar, inputs))
        except Invalid:
            continue
    require(len(valid) == 1, "ambiguous/mixed problem fields")
    ar, inputs = valid[0]
    by_assertion = {}
    for origin, value in zip(problem.origins, inputs):
        by_assertion[origin] = value
    known, assumptions = {}, {}
    steps = parse(proof_text)
    require(0 < len(steps) <= 104096, "Alethe step limit")
    ended = False
    for step in steps:
        require(not ended and isinstance(step, list) and len(step) >= 3, "malformed/trailing Alethe step")
        key = symbol(step[1]); require(key not in known and key not in assumptions, "duplicate proof ID")
        if step[0] == 'assume':
            require(len(step) == 3 and step[2] in problem.assertions, "unasserted assumption")
            assumptions[key] = problem.assertions.index(step[2])
            continue
        require(step[0] == 'step', "unsupported Alethe command")
        attrs = attributes(step[3:], {':rule', ':premises', ':args'})
        rule, premises, args = attrs[':rule'], attrs[':premises'], attrs[':args']
        require(isinstance(premises, list) and isinstance(args, list), "malformed rule parameters")
        premises = list(map(symbol, premises))
        if rule == 'ff_poly_input':
            require(len(premises) == 1 and premises[0] in assumptions and len(args) == 1, "invalid input rule")
            origin = (assumptions[premises[0]], natural(args[0]))
            require(origin in by_assertion, "invalid conjunction projection")
            value = by_assertion[origin]
        else:
            require(all(x in known for x in premises), "unknown/forward premise")
            if rule == 'ff_poly_add':
                require(len(premises) == 2 and not args, "invalid addition rule")
                value = ar.add(known[premises[0]], known[premises[1]])
            elif rule == 'ff_poly_mul':
                require(len(premises) == 1 and len(args) == 1, "invalid multiplication rule")
                value = ar.mul(known[premises[0]], problem.term(args[0], names, ar))
            elif rule == 'ff_poly_contra':
                require(len(premises) == 1 and not args and step[2] == ['cl'] and known[premises[0]] == {(): 1}, "invalid contradiction rule")
                ended = True
                continue
            else:
                raise Invalid("unsupported Alethe rule (holes are rejected)")
        require(isinstance(step[2], list) and len(step[2]) == 2 and step[2][0] == 'cl', "expected unit clause")
        require(problem.equation(step[2][1], names, ar) == value, "incorrect Alethe conclusion")
        known[key] = ar.keep(value)
    require(ended, "missing final contradiction")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('problem', type=Path)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--alethe', action='store_true', help='check experimental ff-poly-v1 Alethe extension')
    parser.add_argument('--export-alethe', type=Path, help='check the DAG, then export and check the Alethe extension')
    args = parser.parse_args()
    start = time.perf_counter()
    try:
        problem, certificate = args.problem.read_text(), args.certificate.read_text()
        if args.alethe:
            require(not args.export_alethe, 'cannot re-export Alethe input')
            verify_alethe(problem, certificate)
        else:
            verify(problem, certificate)
            if args.export_alethe:
                output = export_alethe(problem, certificate)
                verify_alethe(problem, output)
                args.export_alethe.write_text(output)
        print(f'valid polynomial refutation ({time.perf_counter() - start:.3f}s)')
    except (Invalid, RecursionError, ValueError, TypeError, IndexError, KeyError, OSError) as error:
        print(f'certificate rejected: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
