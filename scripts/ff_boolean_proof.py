#!/usr/bin/env python3
"""Bounded, input-bound Boolean resolution and FF theory-lemma certificates.

All terms are hash-consed in a typed DAG. Search is untrusted: rechecking
reconstructs the input clauses, checks each field lemma, and replays resolution.
No SAT answer or unrecorded preprocessing step is accepted as evidence.
"""
import json
from pathlib import Path
import re
import time

import ff_certificate as fc

MAX_NODES = 100000
MAX_RECORDS = 50000
MAX_LEMMAS = 256


def require(c, message):
    fc.require(c, message)


def sort_text(p):
    return 'Bool' if p == 0 else f'(_ FiniteField {p})'


def clause(lits):
    return tuple(sorted(set(lits), key=lambda x: (abs(x), x)))


class Graph:
    def __init__(self, text):
        self.nodes = [None]  # Positive node IDs are also Boolean atom IDs.
        self.intern, self.names, self.sorts, self.assertions = {}, {}, {}, []
        self.literal_ids = {}
        self.work = 0
        commands = fc.parse(text, max_depth=100000)
        reserved, pending = set(), list(commands)
        while pending:
            x = pending.pop()
            if isinstance(x, list): pending.extend(x)
            elif not x.startswith('"'): reserved.add(fc.symbol(x))
        self.prefix = 'ff_proof_'
        while any(s.startswith(self.prefix) for s in reserved): self.prefix += '_'
        ended = False
        for cmd in commands:
            require(isinstance(cmd, list) and cmd, 'expected command')
            op = cmd[0]
            if op in ('set-logic', 'set-info', 'set-option'): continue
            if op in ('check-sat', 'ff-certify', 'get-info', 'get-model', 'get-proof', 'get-statistics', 'exit'):
                ended = True
                continue
            require(not ended, 'assertions/declarations after query are unsupported')
            if op == 'define-sort':
                require(len(cmd) == 4 and cmd[2] == [], 'only nullary sorts supported')
                name = fc.symbol(cmd[1]); require(name not in self.sorts, 'duplicate sort')
                self.sorts[name] = self.sort(cmd[3])
            elif op in ('declare-const', 'declare-fun'):
                require((op == 'declare-const' and len(cmd) == 3) or
                        (op == 'declare-fun' and len(cmd) == 4 and cmd[2] == []), 'only constants supported')
                name = fc.symbol(cmd[1]); require(name not in self.names, 'duplicate declaration')
                self.names[name] = self.node('var', (), (cmd[1], self.sort(cmd[-1])))
            elif op == 'define-fun':
                require(len(cmd) == 5 and cmd[2] == [], 'only nullary definitions supported')
                name = fc.symbol(cmd[1]); require(name not in self.names, 'duplicate definition')
                value = self.expand(cmd[4]); require(self.typ(value) == self.sort(cmd[3]), 'definition sort mismatch')
                self.names[name] = value
            elif op == 'assert':
                require(len(cmd) == 2, 'malformed assertion')
                t = self.expand(cmd[1]); require(self.typ(t) == 0, 'assertion must be Boolean')
                self.assertions.append(t)
            else: raise fc.Invalid('unsupported command: ' + str(op))
        require(self.assertions, 'no assertions')
        fields = {self.typ(i) for i in range(1, len(self.nodes)) if self.typ(i)}
        require(len(fields) <= 1, 'mixed fields unsupported')
        self.p = next(iter(fields), 2)
        self.source_nodes = len(self.nodes)
        self.ites = []
        # A field ITE is an opaque field atom in polynomial arithmetic, with
        # its selected value constrained by a checked Boolean ITE tautology.
        for i in range(1, self.source_nodes):
            op, args, _ = self.nodes[i]
            if op == 'ite' and self.typ(i):
                c, a, b = args
                first, second = self.node('=', (i, a)), self.node('=', (i, b))
                meaning = self.node('ite', (c, first, second))
                self.ites.append((i, meaning))
        self.boolean_nodes = len(self.nodes)

    def tick(self):
        self.work += 1; require(self.work <= 2000000, 'front-end work limit')

    def sort(self, s):
        if s == 'Bool': return 0
        if isinstance(s, str):
            require(fc.symbol(s) in self.sorts, 'unknown sort'); return self.sorts[fc.symbol(s)]
        require(isinstance(s, list) and len(s) == 3 and s[:2] == ['_', 'FiniteField'], 'unsupported sort')
        p = fc.natural(s[2]); require(2 <= p and p.bit_length() <= 4096, 'invalid modulus')
        return p

    def typ(self, i):
        op, args, data = self.nodes[i]
        if op in ('var', 'num'): return data[1]
        if op in ('ff.add', 'ff.mul', 'ff.neg', 'ite'): return self.typ_cache[i]
        return 0

    def node(self, op, args=(), data=None):
        self.tick(); args = tuple(args)
        key = (op, args, data)
        if key in self.intern: return self.intern[key]
        if not hasattr(self, 'typ_cache'): self.typ_cache = {}
        if op not in ('var', 'num', 'true', 'false'):
            types = [self.typ(i) for i in args]
            if op in ('and', 'or'): require(len(args) >= 2 and not any(types), 'Boolean connective sort/arity')
            elif op == 'not': require(types == [0], 'negation sort/arity')
            elif op in ('=>', 'xor'): require(types == [0, 0], 'Boolean connective sort/arity')
            elif op == '=': require(len(types) == 2 and types[0] == types[1], 'equality sort/arity')
            elif op == 'ite': require(len(types) == 3 and types[0] == 0 and types[1] == types[2], 'ITE sort/arity')
            elif op in ('ff.add', 'ff.mul', 'ff.neg'):
                require(len(types) >= (1 if op == 'ff.neg' else 2) and types[0] and len(set(types)) == 1
                        and (op != 'ff.neg' or len(types) == 1), 'field operator sort/arity')
            else: raise fc.Invalid('unsupported term: ' + str(op))
        require(len(self.nodes) < MAX_NODES, 'term DAG limit')
        i = len(self.nodes); self.nodes.append(key); self.intern[key] = i
        self.literal_ids[i] = -self.literal_ids[args[0]] if op == 'not' else i
        if op in ('ff.add', 'ff.mul', 'ff.neg'): self.typ_cache[i] = self.typ(args[0])
        if op == 'ite': self.typ_cache[i] = self.typ(args[1])
        return i

    def expand(self, root):
        # Explicit frames preserve simultaneous let semantics and lexical scope.
        # Bindings reference DAG IDs; expanding nested/shared lets never copies
        # their expression trees and does not use the Python call stack.
        tasks, values = [('visit', root)], []
        env = dict(self.names)
        while tasks:
            self.tick(); kind, x = tasks.pop()
            if kind == 'restore':
                for name, old in x:
                    if old is None: env.pop(name, None)
                    else: env[name] = old
            elif kind == 'bind':
                bindings, body = x; count = len(bindings)
                ids = values[-count:] if count else []
                if count: del values[-count:]
                old = [(name, env.get(name)) for name in bindings]
                env.update(zip(bindings, ids))
                tasks.extend([('restore', old), ('visit', body)])
            elif kind == 'make':
                op, n = x; ids = values[-n:] if n else []
                if n: del values[-n:]
                values.append(self.node(op, ids))
            elif kind == 'as':
                require(self.typ(values[-1]) == x, 'ascription sort mismatch')
            elif isinstance(x, str):
                if x in ('true', 'false'): values.append(self.node(x)); continue
                m = re.fullmatch(r'#f(-?[0-9]+)m([0-9]+)', x)
                if m:
                    p = fc.natural(m[2]); require(2 <= p and p.bit_length() <= 4096, 'invalid modulus')
                    require(len(m[1]) <= 1301, 'numeral limit')
                    values.append(self.node('num', data=(int(m[1]), p))); continue
                require(fc.symbol(x) in env, 'undeclared constant'); values.append(env[fc.symbol(x)])
            else:
                require(isinstance(x, list) and x and isinstance(x[0], str), 'unsupported term')
                op = x[0]
                if op == 'let':
                    require(len(x) == 3 and isinstance(x[1], list), 'malformed let')
                    bs = x[1]; require(all(isinstance(b, list) and len(b) == 2 for b in bs), 'malformed binding')
                    names = [fc.symbol(b[0]) for b in bs]; require(len(set(names)) == len(names), 'duplicate binding')
                    tasks.append(('bind', (names, x[2])))
                    tasks.extend(('visit', b[1]) for b in reversed(bs))
                elif op == '!':
                    require(len(x) >= 4 and len(x) % 2 == 0 and all(x[j] == ':named' for j in range(2, len(x), 2)), 'unsupported annotation')
                    tasks.append(('visit', x[1]))
                elif op == 'as':
                    require(len(x) == 3, 'malformed ascription'); p = self.sort(x[2])
                    if isinstance(x[1], str) and re.fullmatch(r'ff-?[0-9]+', x[1]):
                        require(p and len(x[1]) <= 1303, 'invalid field numeral')
                        values.append(self.node('num', data=(int(x[1][2:]), p)))
                    else: tasks.extend([('as', p), ('visit', x[1])])
                else:
                    tasks.append(('make', (op, len(x) - 1)))
                    tasks.extend(('visit', a) for a in reversed(x[1:]))
        require(len(values) == 1, 'expansion stack mismatch')
        return values[0]

    def ref(self, i):
        op, args, data = self.nodes[i]
        if op == 'var': return data[0]
        if op == 'num': return f'(as ff{data[0]} {sort_text(data[1])})'
        if op in ('true', 'false'): return op
        return f'{self.prefix}t{i}'

    def literal(self, i):
        return self.ref(i) if i > 0 else f'(not {self.ref(-i)})'

    def lit(self, i):
        return self.literal_ids[i]

    def definitions(self):
        return [f'(define-fun {self.ref(i)} () {sort_text(self.typ(i))} '
                f'({op} {" ".join(self.ref(a) for a in args)}))'
                for i, (op, args, data) in enumerate(self.nodes[1:], 1) if args]

    def field_atom(self, i):
        op, args, _ = self.nodes[abs(i)]
        return op == '=' and self.typ(args[0]) != 0


class Clauses:
    def __init__(self, g):
        self.g, self.clauses, self.sources = g, [], []
        for n, a in enumerate(g.assertions): self.add([g.lit(a)], ('assume', n, a))
        for i in range(1, g.boolean_nodes):
            op, args, _ = g.nodes[i]
            if g.typ(i) or op in ('var', 'not'): continue
            a = list(args)
            if op == 'true': self.add([i], ('rule', 'true', [i], None))
            elif op == 'false': self.add([-i], ('rule', 'false', [-i], None))
            elif op in ('and', 'or'):
                # Clauses are the defining truth table, not guessed rewrites.
                for j, child in enumerate(a):
                    raw = [-i, child] if op == 'and' else [i, -child]
                    self.add(raw, ('rule', op + ('_pos' if op == 'and' else '_neg'), raw, [str(j)]))
                raw = [i] + [-x for x in a] if op == 'and' else [-i] + a
                self.add(raw, ('rule', op + ('_neg' if op == 'and' else '_pos'), raw, None))
            elif op == '=>':
                for rule, raw in [('implies_pos', [-i, -a[0], a[1]]), ('implies_neg1', [i, a[0]]), ('implies_neg2', [i, -a[1]])]:
                    self.add(raw, ('rule', rule, raw, None))
            elif op in ('=', 'xor') and not g.field_atom(i):
                rows = [('pos1', [-i, a[0], -a[1]]), ('pos2', [-i, -a[0], a[1]]),
                        ('neg1', [i, -a[0], -a[1]]), ('neg2', [i, a[0], a[1]])]
                if op == 'xor':
                    rows = [('pos1', [-i, a[0], a[1]]), ('pos2', [-i, -a[0], -a[1]]),
                            ('neg1', [i, a[0], -a[1]]), ('neg2', [i, -a[0], a[1]])]
                for suffix, raw in rows: self.add(raw, ('rule', ('equiv' if op == '=' else 'xor') + '_' + suffix, raw, None))
            elif op == 'ite':
                for rule, raw in [('ite_pos1', [-i, a[0], a[2]]), ('ite_pos2', [-i, -a[0], a[1]]),
                                  ('ite_neg1', [i, a[0], -a[2]]), ('ite_neg2', [i, -a[0], -a[1]])]:
                    self.add(raw, ('rule', rule, raw, None))
        for i, meaning in g.ites: self.add([meaning], ('ite', i, meaning))

    def add(self, raw, source):
        self.clauses.append(clause((1 if x > 0 else -1) * self.g.lit(abs(x)) for x in raw)); self.sources.append(source)
        require(len(self.clauses) <= MAX_RECORDS, 'clause limit')


def resolve(a, b, pivot):
    require(type(pivot) is int and pivot in a and -pivot in b, 'invalid resolution pivot')
    return clause([x for x in a if x != pivot] + [x for x in b if x != -pivot])


class Search:
    def __init__(self, clauses):
        self.clauses = list(clauses)
        self.records, self.work = [], 0
        self.active = list(range(len(self.clauses)))
        self.by_clause = {c: i for i, c in enumerate(self.clauses)}

    def append(self, c, record):
        # Reusing a globally proved clause preserves its proof and avoids
        # recording the same propagation conflict again after each theory lemma.
        if record['rule'] == 'resolve' and c in self.by_clause:
            return self.by_clause[c]
        require(len(self.records) < MAX_RECORDS, 'resolution record limit')
        self.records.append(record); self.clauses.append(c)
        self.by_clause[c] = len(self.clauses) - 1
        if record['rule'] == 'field': self.active.append(len(self.clauses) - 1)
        return len(self.clauses) - 1

    def resolution(self, a, b, pivot):
        return self.append(resolve(self.clauses[a], self.clauses[b], pivot), dict(rule='resolve', left=a, right=b, pivot=pivot))

    def search(self, assignment=None, reasons=None, trail=None, depth=0):
        require(depth < 256, 'Boolean decision depth limit')
        assignment = {} if assignment is None else assignment.copy()
        reasons = {} if reasons is None else reasons.copy()
        trail = [] if trail is None else trail.copy()
        while True:
            changed, best = False, None
            for index in self.active:
                c = self.clauses[index]
                self.work += len(c) + 1; require(self.work <= 10000000, 'Boolean search work limit')
                if any(assignment.get(abs(x)) == (x > 0) for x in c): continue
                unknown = [x for x in c if abs(x) not in assignment]
                if not unknown:
                    # Resolve only propagated literals. The resulting clause
                    # mentions decisions alone and is valid without assuming them.
                    result = index
                    for lit in reversed(trail):
                        if -lit in self.clauses[result] and abs(lit) in reasons:
                            result = self.resolution(result, reasons[abs(lit)], -lit)
                    return False, result
                if len(unknown) == 1:
                    x = unknown[0]; assignment[abs(x)] = x > 0; reasons[abs(x)] = index; trail.append(x)
                    changed = True
                elif best is None or len(unknown) < len(best): best = unknown
            if not changed: break
        if best is None: return True, assignment
        pivot = best[0]
        left_assignment = assignment | {abs(pivot): pivot > 0}
        sat, left = self.search(left_assignment, reasons, trail + [pivot], depth + 1)
        if sat: return True, left
        if -pivot not in self.clauses[left]: return False, left
        sat, right = self.search(assignment | {abs(pivot): pivot < 0}, reasons, trail + [-pivot], depth + 1)
        if sat: return True, right
        if pivot not in self.clauses[right]: return False, right
        return False, self.resolution(left, right, -pivot)


class Case:
    """Independent polynomial view of precisely the lemma's field literals."""
    def __init__(self, g, literals):
        require(isinstance(literals, list) and 0 < len(literals) <= 4096, 'field lemma input limit')
        require(all(type(x) is int and 0 < abs(x) < g.boolean_nodes and g.field_atom(x) for x in literals), 'non-field lemma premise')
        require(len({abs(x) for x in literals}) == len(literals), 'duplicate/opposite lemma premises')
        self.g, self.equations = g, literals
        self.used = set()
        pending = [a for lit in literals for a in g.nodes[abs(lit)][1]]
        while pending:
            i = pending.pop()
            if i in self.used: continue
            self.used.add(i)
            op, args, _ = g.nodes[i]
            if op != 'ite': pending.extend(args)
        self.declarations = {self.variable(i): (self.variable(i), g.p) for i in sorted(self.used)
                             if g.nodes[i][0] in ('var', 'ite')}
        self.declarations.update({self.witness(x): (self.witness(x), g.p) for x in literals if x < 0})
        self.cache = {}

    def variable(self, i): return f'{self.g.prefix}v{i}'
    def witness(self, lit): return f'{self.g.prefix}w{abs(lit)}'

    def ref(self, i):
        op, args, data = self.g.nodes[i]
        if op in ('var', 'ite'): return self.variable(i)
        if op == 'num': return self.g.ref(i)
        return f'{self.g.prefix}f{i}'

    def eq_text(self, lit):
        a, b = self.g.nodes[abs(lit)][1]
        if lit > 0: return f'(= {self.ref(a)} {self.ref(b)})'
        p = self.g.p
        return f'(= (ff.add (ff.mul (ff.add {self.ref(a)} (ff.neg {self.ref(b)})) {self.witness(lit)}) (as ff{p-1} {sort_text(p)})) (as ff0 {sort_text(p)}))'

    def normalized(self):
        out = ['(set-logic QF_FF)']
        out += [f'(declare-const {name} {sort_text(p)})' for name, p in self.declarations.values()]
        for i in sorted(self.used):
            op, args, _ = self.g.nodes[i]
            if op.startswith('ff.'):
                out.append(f'(define-fun {self.ref(i)} () {sort_text(self.g.p)} ({op} {" ".join(self.ref(a) for a in args)}))')
        out += [f'(assert {self.eq_text(lit)})' for lit in self.equations]
        text = '\n'.join(out) + '\n'; require(len(text) <= 32*1024*1024, 'case input size limit')
        return text

    def equation(self, lit, names, ar):
        g = self.g
        require(ar.p == g.p, 'field lemma modulus differs from original input')
        # Bottom-up evaluation uses shared child values and no recursive calls.
        if not self.cache:
            for i in sorted(self.used):
                op, args, data = g.nodes[i]
                if op in ('var', 'ite'):
                    require(self.variable(i) in names, 'missing field variable')
                    value = {(names[self.variable(i)],): 1}
                elif op == 'num':
                    c = data[0] % ar.p; value = {(): c} if c else {}
                elif op == 'ff.neg': value = ar.add({}, self.cache[args[0]], -1)
                else:
                    value = {(): 1} if op == 'ff.mul' else {}
                    for a in args:
                        value = ar.mul(value, self.cache[a]) if op == 'ff.mul' else ar.add(value, self.cache[a])
                self.cache[i] = ar.keep(value)
        a, b = g.nodes[abs(lit)][1]
        value = ar.add(self.cache[a], self.cache[b], -1)
        if lit < 0:
            require(self.witness(lit) in names, 'missing inverse witness')
            value = ar.add(ar.mul(value, {(names[self.witness(lit)],): 1}), {(): 1}, -1)
        return value

    def choice(self, lit):
        g = self.g; a, b = g.nodes[abs(lit)][1]; binder = f'{g.prefix}bound{abs(lit)}'
        return f'(choice (({binder} {sort_text(g.p)})) (= (ff.mul {binder} (ff.add {g.ref(a)} (ff.neg {g.ref(b)}))) (as ff1 {sort_text(g.p)})))'

    def original_variables(self, variables):
        mapping = {self.variable(i): self.g.ref(i) for i in self.used if self.g.nodes[i][0] in ('var', 'ite')}
        mapping.update({self.witness(x): self.choice(x) for x in self.equations if x < 0})
        return [mapping[x] for x in variables]


def compact(g, literals, dag):
    _, cert, _ = fc.verify_problem(Case(g, literals), dag)
    nodes, used, pending = cert[':nodes'], set(), [int(cert[':root'])]
    while pending:
        i = pending.pop()
        if i in used: continue
        used.add(i); n = nodes[i]
        if n[0] == 'add': pending.extend([int(n[1]), int(n[2])])
        elif n[0] == 'mul': pending.append(int(n[1]))
    inputs = sorted({int(nodes[i][1]) for i in used if nodes[i][0] == 'input'})
    input_map = {x: str(j) for j, x in enumerate(inputs)}
    node_map = {x: str(j) for j, x in enumerate(sorted(used))}
    new_nodes = []
    for i in sorted(used):
        n = list(nodes[i])
        if n[0] == 'input': n[1] = input_map[int(n[1])]
        else:
            n[1] = node_map[int(n[1])]
            if n[0] == 'add': n[2] = node_map[int(n[2])]
        new_nodes.append(n)
    cert[':inputs'] = [cert[':inputs'][i] for i in inputs]
    cert[':nodes'], cert[':root'] = new_nodes, node_map[int(cert[':root'])]
    core = [literals[i] for i in inputs]
    # Remove variables absent from the core only if they are not used anywhere
    # in the certificate. Keeping declarations for prior nodes is unnecessary;
    # renumber every monomial with the surviving original variable names.
    case = Case(g, core)
    old_variables = cert[':variables']
    used_vars = [i for i, x in enumerate(old_variables) if x in case.declarations]
    renumber = {x: str(j) for j, x in enumerate(used_vars)}
    cert[':variables'] = [old_variables[i] for i in used_vars]
    for f in cert[':inputs']:
        for t in f: t[1:] = [renumber[int(v)] for v in t[1:]]
    for n in cert[':nodes']:
        if n[0] == 'mul': n[3] = [renumber[int(v)] for v in n[3]]
    result = fc.sexpr(['ff-certificate'] + [x for kv in cert.items() for x in kv]) + '\n'
    fc.verify_problem(case, result)
    return core, result


def produce(original, z3, timeout):
    import ff_proof_pipeline as pp
    start = time.monotonic(); g = Graph(original); base = Clauses(g); search = Search(base.clauses)
    lemmas = 0
    while True:
        require(time.monotonic() - start < timeout, 'Boolean pipeline timeout')
        sat, result = search.search()
        if not sat:
            require(search.clauses[result] == (), 'incomplete Boolean refutation')
            # Export only ancestors of the final contradiction. Search's
            # discarded Boolean branches are not proof premises.
            offset = len(base.clauses)
            used, pending = set(), [result]
            while pending:
                i = pending.pop()
                if i < offset or i in used: continue
                used.add(i); record = search.records[i - offset]
                if record['rule'] == 'resolve': pending.extend([record['left'], record['right']])
            mapping = {old: offset + j for j, old in enumerate(sorted(used))}
            records = []
            for i in sorted(used):
                record = dict(search.records[i - offset])
                if record['rule'] == 'resolve':
                    for key in ['left', 'right']: record[key] = mapping.get(record[key], record[key])
                records.append(record)
            return dict(version=2, records=records, root=mapping.get(result, result))
        require(lemmas < MAX_LEMMAS, 'field lemma count limit')
        literals = sorted([i if v else -i for i, v in result.items() if g.field_atom(i)], key=abs)
        require(literals, 'no field conflict (possibly satisfiable)')
        case = Case(g, literals)
        remaining = timeout - (time.monotonic() - start); require(remaining > 0, 'Boolean pipeline timeout')
        output = pp.run([str(z3), '-in'], remaining, case.normalized() + f'(ff-certify :timeout {max(1,int(remaining*900))})\n')['stdout']
        require(output.startswith('(ff-certificate\n'), 'field certificate unavailable: ' + output[:300].strip())
        core, dag = compact(g, literals, output)
        search.append(clause(-x for x in core), dict(rule='field', literals=core, certificate=dag))
        lemmas += 1


class Writer:
    def __init__(self, g):
        self.g, self.lines, self.next, self.bytes = g, [], 0, 0
        self.emit('; z3-ff-alethe-pac-v2: input-bound Boolean resolution.')
        for line in g.definitions(): self.emit(line)
        self.names = []
        self.false = None

    def emit(self, text):
        self.bytes += len(text.encode()) + 1
        require(self.bytes <= 32*1024*1024, 'Alethe output size limit')
        self.lines.append(text)

    def step(self, terms, rule, premises=(), args=None, name=None, discharge=None):
        if name is None: name = f'{self.g.prefix}s{self.next}'; self.next += 1
        s = f'(step {name} (cl {" ".join(terms)}) :rule {rule}'
        if premises: s += ' :premises (' + ' '.join(premises) + ')'
        if args is not None: s += ' :args (' + ' '.join(args) + ')'
        if discharge is not None: s += ' :discharge (' + ' '.join(discharge) + ')'
        self.emit(s + ')'); return name

    def transfer(self, source, target, eq, premise):
        imp = self.step([f'(not {source})', target], 'equiv1', [eq])
        return self.step([target], 'resolution', [imp, premise])

    def base(self, clauses):
        g = self.g
        for c, src in zip(clauses.clauses, clauses.sources):
            if src[0] == 'assume':
                _, n, i = src; name = f'{g.prefix}a{n}'
                self.emit(f'(assume {name} {g.ref(i)})')
            elif src[0] == 'rule':
                _, rule, raw, args = src
                name = self.step([g.literal(x) for x in raw], rule, args=args)
            else:
                _, i, meaning = src
                # ite_intro proves true iff true AND the ITE defining equation.
                # Transfer true, then project the second conjunct. This uses
                # existing Carcara rules and introduces no unchecked axiom.
                truth = self.step(['true'], 'true')
                target = f'(and true {g.ref(meaning)})'
                eq = self.step([f'(= true {target})'], 'ite_intro')
                conj = self.transfer('true', target, eq, truth)
                name = self.step([g.ref(meaning)], 'and', [conj], ['1'])
            self.names.append(name)
        self.false = self.step(['(not false)'], 'false')

    def field(self, record, index):
        import ff_proof_pipeline as pp
        g = self.g; literals, dag = record['literals'], record['certificate']
        case = Case(g, literals)
        _, cert, values = fc.verify_problem(case, dag)
        variables, p = case.original_variables(cert[':variables']), g.p
        def poly(value): return fc.sexpr(fc.polynomial_term(value, p, variables))
        zero, one = f'(as ff0 {sort_text(p)})', f'(as ff1 {sort_text(p)})'
        lemma = f'{g.prefix}lemma{index}'
        self.emit(f'(anchor :step {lemma})')
        assumptions, normalized, proofs, polynomials = [], [], [], []
        for j, lit in enumerate(literals):
            name = f'{lemma}_a{j}'
            self.emit(f'(assume {name} {g.literal(lit)})'); assumptions.append(name)
        for j, lit in enumerate(literals):
            name = assumptions[j]; literal = g.literal(lit)
            a, b = g.nodes[abs(lit)][1]; a, b = g.ref(a), g.ref(b)
            if lit < 0:
                choice = case.choice(lit)
                value = f'(ff.add (ff.mul (ff.add {a} (ff.neg {b})) {choice}) (as ff{p-1} {sort_text(p)}))'
                equation = f'(= {value} {zero})'
                eq = self.step([f'(= {literal} {equation})'], 'ff_diseq', args=[a,b,choice])
                name = self.transfer(literal, equation, eq, name); a, b = value, zero
            else: equation = literal
            value = fc.decode_polynomial(cert[':inputs'][j], fc.Arithmetic(p), len(variables))
            polynomial = poly(value); polynomials.append(polynomial)
            canonical = f'(= {polynomial} {zero})'; normalized.append(canonical)
            identity = f'(= (ff.mul {one} (ff.add {a} (ff.neg {b}))) (ff.mul {one} (ff.add {polynomial} (ff.neg {zero}))))'
            identity_step = self.step([identity], 'poly_simp')
            equivalence = self.step([f'(= {equation} {canonical})'], 'poly_simp_rel', [identity_step])
            proofs.append(self.transfer(equation, canonical, equivalence, name))
        conj = proofs[0] if len(proofs) == 1 else self.step(['(and ' + ' '.join(normalized) + ')'], 'and_intro', proofs)
        conversion = self.step(['(not (set.is_empty (@ff.variety (@ff.ideal ' + ' '.join(polynomials) + '))))'], 'ff_poly_conversion', [conj])
        pac = pp.export_pac(cert, values)
        self.step([], 'ff_pac', [conversion], [pac])
        discharged = [f'(not {g.literal(x)})' for x in literals] + ['false']
        self.step(discharged, 'subproof', name=lemma, discharge=assumptions)
        final = self.step([g.literal(-x) for x in literals], 'resolution', [lemma, self.false])
        return final, case.normalized(), pac


def verify_export(original, proof):
    require(isinstance(proof, dict) and set(proof) == {'version', 'records', 'root'} and proof['version'] == 2, 'unknown Boolean certificate schema')
    require(isinstance(proof['records'], list) and len(proof['records']) <= MAX_RECORDS, 'record limit')
    g = Graph(original); base = Clauses(g); clauses = list(base.clauses); writer = Writer(g); writer.base(base)
    files, count = {}, 0
    for record in proof['records']:
        require(isinstance(record, dict), 'malformed record')
        if record.get('rule') == 'field':
            require(set(record) == {'rule','literals','certificate'} and isinstance(record['certificate'], str), 'malformed field record')
            count += 1; require(count <= MAX_LEMMAS, 'field lemma count limit')
            name, normalized, pac = writer.field(record, count)
            files[f'lemma-{count:04d}.smt2'] = normalized; files[f'lemma-{count:04d}.pac'] = pac
            value = clause(-x for x in record['literals'])
        else:
            require(set(record) == {'rule','left','right','pivot'} and record['rule'] == 'resolve', 'malformed resolution record')
            a, b, pivot = record['left'], record['right'], record['pivot']
            require(type(a) is int and type(b) is int and 0 <= a < len(clauses) and 0 <= b < len(clauses), 'forward/invalid resolution reference')
            value = resolve(clauses[a], clauses[b], pivot)
            name = writer.step([g.literal(x) for x in value], 'resolution', [writer.names[a], writer.names[b]])
        clauses.append(value); writer.names.append(name)
    root = proof['root']; require(type(root) is int and 0 <= root < len(clauses) and clauses[root] == (), 'Boolean root is not empty')
    # The file must end with the checked root even when search recorded later
    # unused work. Reordering is a checked existing Alethe rule, not a new admission.
    writer.step([], 'reordering', [writer.names[root]])
    files['proof.alethe'] = '\n'.join(writer.lines) + '\n'
    require(sum(len(v.encode()) for v in files.values()) <= 32*1024*1024, 'Boolean bundle export size limit')
    return files


def produce_bundle(original, directory, z3, timeout):
    proof = produce(original, z3, timeout)
    files = verify_export(original, proof)
    files['boolean-certificate.json'] = json.dumps(proof, separators=(',', ':')) + '\n'
    require(len(files['boolean-certificate.json']) <= 32*1024*1024, 'Boolean certificate size limit')
    for name, text in files.items(): (Path(directory) / name).write_text(text)
    return len([r for r in proof['records'] if r['rule'] == 'field'])


def check_bundle(directory, carcara, ffpacheck, timeout):
    import ff_proof_pipeline as pp
    directory = Path(directory)
    files = verify_export(pp.read(directory/'problem.smt2'), json.loads(pp.read(directory/'boolean-certificate.json')))
    for name, expected in files.items(): require(pp.read(directory/name) == expected, 'Boolean input/proof binding mismatch: '+name)
    pac_runs = [pp.run([str(ffpacheck), str(directory/name)], timeout) for name in files if name.endswith('.pac')]
    result = pp.run([str(carcara), 'check', str(directory/'proof.alethe'), str(directory/'problem.smt2'),
                     '--expand-let-bindings', '--apply-function-defs', '--ff-pac-solver', str(ffpacheck)], timeout)
    require(result['stdout'].strip() == 'valid', 'Carcara did not report valid')
    return dict(carcara=result, ffpacheck=dict(seconds=sum(r['seconds'] for r in pac_runs), returncode=0, lemmas=len(pac_runs), runs=pac_runs))
