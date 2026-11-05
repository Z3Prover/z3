#!/usr/bin/env python3
"""Bounded, input-bound Boolean resolution and FF theory-lemma certificates.

All terms are hash-consed in a typed DAG. Search is untrusted: rechecking
reconstructs the input clauses, checks each field lemma, and replays resolution.
No SAT answer or unrecorded preprocessing step is accepted as evidence.
"""
import json
import os
from pathlib import Path
import re
import time

import ff_certificate as fc

MAX_NODES = 100000
MAX_RECORDS = 50000
MAX_LEMMAS = 1024


def require(c, message):
    fc.require(c, message)


def sort_text(p):
    return 'Bool' if p == 0 else f'(_ FiniteField {p})'


def clause(lits):
    return tuple(sorted(set(lits), key=lambda x: (abs(x), x)))


class Graph:
    def __init__(self, text, ranges=False, compounds=False):
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
        self.cut_definitions = {}
        self.range_seeds = []
        if ranges:
            import ff_range_proof
            ff_range_proof.augment(self, compounds=compounds)
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
        result = []
        for i, (op, args, data) in enumerate(self.nodes[1:], 1):
            if i in self.cut_definitions:
                body = self.ref(self.cut_definitions[i])
            elif args:
                body = f'({op} {" ".join(self.ref(a) for a in args)})'
            else:
                continue
            result.append(f'(define-fun {self.ref(i)} () {sort_text(self.typ(i))} {body})')
        return result

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
        for i, value in g.cut_definitions.items():
            atom = g.node('=', (i, value))
            self.add([atom], ('cut', atom))

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
        self.active_set = set(self.active)

    def append(self, c, record):
        # Reusing a globally proved clause preserves its proof and avoids
        # recording the same propagation conflict again after each theory lemma.
        if record['rule'] == 'resolve' and c in self.by_clause:
            return self.by_clause[c]
        require(len(self.records) < MAX_RECORDS, 'resolution record limit')
        self.records.append(record); self.clauses.append(c)
        self.by_clause[c] = len(self.clauses) - 1
        if record['rule'] == 'field': self.activate(len(self.clauses) - 1)
        return len(self.clauses) - 1

    def activate(self, index):
        # Every learned clause has an explicit, globally valid resolution
        # derivation. Reusing it in propagation adds no unproved assumption.
        if index not in self.active_set:
            self.active.append(index); self.active_set.add(index)
        return index

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
                    return False, self.activate(result)
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
        return False, self.activate(self.resolution(left, right, -pivot))


class NativeSearch(Search):
    """Use native CDCL, then elaborate its clause evidence into resolution.

    Only independently reconstructed RUP consequences enter the proof. Native
    clauses are never promoted to assumptions, even if labelled input by SAT.
    """
    def __init__(self, clauses, z3, deadline):
        super().__init__(clauses)
        self.z3, self.deadline = z3, deadline

    def rup(self, candidate):
        if candidate in self.by_clause:
            return self.activate(self.by_clause[candidate])
        assignment = {abs(x): x < 0 for x in candidate}
        reasons, trail = {}, []
        while True:
            changed = False
            for index in self.active:
                c = self.clauses[index]
                self.work += len(c) + 1
                require(self.work <= 10000000, 'native Boolean replay work limit')
                if any(assignment.get(abs(x)) == (x > 0) for x in c): continue
                unknown = [x for x in c if abs(x) not in assignment]
                if not unknown:
                    result = index
                    for lit in reversed(trail):
                        if -lit in self.clauses[result]:
                            result = self.resolution(result, reasons[abs(lit)], -lit)
                    require(set(self.clauses[result]) <= set(candidate), 'native RUP conclusion mismatch')
                    # A stronger subclause is sufficient and needs no trusted
                    # weakening step; subsequent RUP checks can use it directly.
                    self.by_clause[candidate] = result
                    return self.activate(result)
                if len(unknown) == 1:
                    lit = unknown[0]
                    assignment[abs(lit)] = lit > 0
                    reasons[abs(lit)] = index
                    trail.append(lit)
                    changed = True
            require(changed, 'native SAT step is not supported by RUP replay')

    def query(self, variables):
        import ff_proof_pipeline as pp
        remaining = self.deadline - time.monotonic()
        require(remaining > 0, 'Boolean pipeline timeout')
        names = {f'b{i}': i for i in variables}
        text = '(set-logic QF_UF)\n' + ''.join(f'(declare-const {name} Bool)\n' for name in names)
        for index in self.active:
            c = self.clauses[index]
            terms = [f'b{x}' if x > 0 else f'(not b{-x})' for x in c]
            body = 'false' if not terms else terms[0] if len(terms) == 1 else '(or ' + ' '.join(terms) + ')'
            text += f'(assert {body})\n'
        text += f'(ff-boolean-certify :timeout {max(1, int(remaining * 900))})\n'
        require(len(text) < 32 * 1024 * 1024, 'native Boolean input size limit')
        return pp.run([str(self.z3), '-in'], remaining, text)['stdout']

    def close(self):
        pass

    def search(self):
        variables = sorted({abs(x) for i in self.active for x in self.clauses[i]})
        names = {f'b{i}': i for i in variables}
        output = self.query(variables)
        objects = fc.parse(output)
        require(len(objects) == 1 and isinstance(objects[0], list), 'invalid native SAT response')
        obj = objects[0]
        require(len(obj) == 9 and obj[0] == 'ff-boolean-result' and
                obj[1::2] == [':status', ':variables', ':model', ':clauses'], 'invalid native SAT response')
        status, native_names, model, trace = obj[2::2]
        require(isinstance(native_names, list) and all(isinstance(x, str) for x in native_names) and
                len(set(native_names)) == len(native_names) and
                set(native_names) == set(names), 'native SAT variable binding mismatch')
        mapping = {i + 1: names[name] for i, name in enumerate(native_names)}
        if status == 'sat':
            require(isinstance(model, list) and len(model) == len(native_names) and
                    all(x in ('true', 'false') for x in model), 'invalid native SAT model')
            assignment = {mapping[i + 1]: value == 'true' for i, value in enumerate(model)}
            require(all(any(assignment[abs(x)] == (x > 0) for x in self.clauses[i]) for i in self.active),
                    'native SAT model does not satisfy Boolean clauses')
            # Keep a partial model that still satisfies every clause. This
            # avoids sending irrelevant total-model field assignments to the
            # algebra layer; no clause may lose its last satisfying literal.
            supports = {v: [] for v in assignment}
            counts = {}
            for index in self.active:
                satisfied = [abs(x) for x in self.clauses[index] if assignment[abs(x)] == (x > 0)]
                counts[index] = len(satisfied)
                for v in satisfied: supports[v].append(index)
            for v in sorted(assignment, reverse=True):
                if all(counts[i] > 1 for i in supports[v]):
                    for i in supports[v]: counts[i] -= 1
                    del assignment[v]
            return True, assignment
        require(status == 'unsat' and isinstance(trace, list) and len(trace) <= 100000,
                'native Boolean search incomplete')
        return self.replay_trace(mapping, trace)

    def replay_trace(self, mapping, trace):
        require(isinstance(trace, list) and len(trace) <= 100000, 'native SAT trace limit')
        for raw in trace:
            require(isinstance(raw, list), 'invalid native SAT clause')
            values = []
            for atom in raw:
                require(isinstance(atom, str) and atom.lstrip('-').isdigit(), 'invalid native SAT literal')
                lit = int(atom)
                require(abs(lit) in mapping, 'unbound native SAT literal')
                values.append(mapping[abs(lit)] * (1 if lit > 0 else -1))
            unique = set(values)
            if any(-lit in unique for lit in unique): continue  # tautology has no useful consequences
            index = self.rup(clause(values))
            if not self.clauses[index]: return False, index
        # Some native UNSAT paths finish with a unit conflict rather than a
        # separately emitted empty clause. It must still replay by propagation.
        return False, self.rup(())


class WatchedSearch(NativeSearch):
    """Watched-literal RUP replay for native CDCL evidence."""
    def replay_trace(self, mapping, trace):
        # All field clauses already have independently replayable certificates.
        # If they close by unit propagation, elaborate that smaller refutation
        # directly. Failure adds no clauses; replay the native trace as before.
        # Work remains charged to the same budget on both paths.
        require(isinstance(trace, list) and len(trace) <= 100000, 'native SAT trace limit')
        for raw in trace:
            require(isinstance(raw, list), 'invalid native SAT clause')
            for atom in raw:
                require(isinstance(atom, str) and atom.lstrip('-').isdigit(), 'invalid native SAT literal')
                require(abs(int(atom)) in mapping, 'unbound native SAT literal')
        try:
            return False, self.rup(())
        except fc.Invalid as e:
            if str(e) != 'native SAT step is not supported by RUP replay':
                raise
        return super().replay_trace(mapping, trace)

    def rup(self, candidate):
        if candidate in self.by_clause:
            return self.activate(self.by_clause[candidate])
        # Watches survive only as indices into globally justified clauses;
        # assignments and propagation reasons are fresh for each RUP query.
        # Any two literals are valid watches when starting unassigned, so moving
        # them during one query cannot assume its decisions in a later query.
        if not hasattr(self, '_rup_watches'):
            self._rup_watches, self._rup_pairs = {}, {}
            self._rup_units, self._rup_empty, self._rup_indexed = [], None, 0
        def charge(n=1):
            self.work += n
            require(self.work <= 10000000, 'native Boolean replay work limit')
        while self._rup_indexed < len(self.active):
            index = self.active[self._rup_indexed]
            c = self.clauses[index]; charge(len(c) + 1)
            if not c: self._rup_empty = index
            elif len(c) == 1: self._rup_units.append((c[0], index))
            else:
                self._rup_pairs[index] = [c[0], c[1]]
                for lit in c[:2]: self._rup_watches.setdefault(lit, []).append(index)
            self._rup_indexed += 1
        assignment = {abs(x): x < 0 for x in candidate}
        reasons, trail = {}, []
        def conflict(index):
            result = index
            for lit in reversed(trail):
                if -lit in self.clauses[result]:
                    result = self.resolution(result, reasons[abs(lit)], -lit)
            require(set(self.clauses[result]) <= set(candidate), 'native RUP conclusion mismatch')
            self.by_clause[candidate] = result
            return self.activate(result)
        if self._rup_empty is not None: return conflict(self._rup_empty)
        # Decisions are not resolution premises. Unit implications carry their
        # actual clause and are discharged, in reverse order, at the conflict.
        pending = [-x for x in candidate]
        for lit, reason in self._rup_units:
            charge()
            if abs(lit) in assignment:
                if assignment[abs(lit)] != (lit > 0): return conflict(reason)
            else:
                assignment[abs(lit)] = lit > 0
                reasons[abs(lit)] = reason; trail.append(lit); pending.append(lit)
        cursor = 0
        while cursor < len(pending):
            lit = pending[cursor]; cursor += 1
            watching = self._rup_watches.get(-lit, [])
            i = 0
            while i < len(watching):
                charge(); index = watching[i]; pair = self._rup_pairs[index]
                slot = 0 if pair[0] == -lit else 1
                other = pair[1-slot]
                if assignment.get(abs(other)) == (other > 0): i += 1; continue
                replacement = None
                for x in self.clauses[index]:
                    charge()
                    if x != -lit and x != other and assignment.get(abs(x)) != (x < 0):
                        replacement = x; break
                if replacement is not None:
                    pair[slot] = replacement
                    watching[i] = watching[-1]; watching.pop()
                    self._rup_watches.setdefault(replacement, []).append(index)
                    continue
                i += 1
                if abs(other) in assignment: return conflict(index)
                assignment[abs(other)] = other > 0
                reasons[abs(other)] = index; trail.append(other); pending.append(other)
        raise fc.Invalid('native SAT step is not supported by RUP replay')



class IncrementalSearch(WatchedSearch):
    """Retain the actual native SAT state between checked field lemmas."""
    def __init__(self, clauses, z3, deadline):
        super().__init__(clauses, z3, deadline)
        self.session = None
        self.sent = set()
        self.declared = set()

    def query(self, variables):
        import ff_proof_pipeline as pp
        remaining = self.deadline - time.monotonic()
        require(remaining > 0, 'Boolean pipeline timeout')
        require(self.sent <= self.active_set, 'non-monotone native Boolean session')
        text = ''
        if self.session is None:
            self.session = pp.NativeSession(self.z3)
            text = '(set-logic QF_UF)\n'
        for v in variables:
            if v not in self.declared:
                text += f'(declare-const b{v} Bool)\n'
                self.declared.add(v)
        for index in self.active:
            if index in self.sent: continue
            c = self.clauses[index]
            terms = [f'b{x}' if x > 0 else f'(not b{-x})' for x in c]
            body = 'false' if not terms else terms[0] if len(terms) == 1 else '(or ' + ' '.join(terms) + ')'
            text += f'(assert {body})\n'
            self.sent.add(index)
        text += f'(ff-boolean-certify :incremental true :timeout {max(1, int(remaining * 900))})\n'
        return self.session.exchange(text, self.deadline)

    def close(self):
        if self.session is not None: self.session.close()

    def __del__(self):
        try: self.close()
        except Exception: pass


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

    def equation_values(self, names, ar):
        """Normalize the input DAG with exact last-use accounting.

        Children shared by several terms or equality endpoints remain live until
        their last use. In particular, repeated arguments count as separate uses.
        No proof node or original equation is skipped by this storage policy.
        """
        require(ar.p == self.g.p, 'field lemma modulus differs from original input')
        g, uses, values = self.g, {}, {}
        for i in self.used:
            op, args, _ = g.nodes[i]
            for a in (() if op in ('var', 'ite', 'num') else args):
                uses[a] = uses.get(a, 0) + 1
        for lit in self.equations:
            for a in g.nodes[abs(lit)][1]: uses[a] = uses.get(a, 0) + 1
        def release(i):
            uses[i] -= 1
            if not uses[i]: ar.release(values.pop(i))
        for i in sorted(self.used):
            op, args, data = g.nodes[i]
            if op in ('var', 'ite'):
                require(self.variable(i) in names, 'missing field variable')
                value = {(names[self.variable(i)],): 1}
            elif op == 'num':
                c = data[0] % ar.p; value = {(): c} if c else {}
            elif op == 'ff.neg': value = ar.add({}, values[args[0]], -1)
            else:
                value = {(): 1} if op == 'ff.mul' else {}
                for a in args:
                    value = ar.mul(value, values[a]) if op == 'ff.mul' else ar.add(value, values[a])
            values[i] = ar.keep(value)
            for a in (() if op in ('var', 'ite', 'num') else args): release(a)
        for lit in self.equations:
            a, b = g.nodes[abs(lit)][1]
            value = ar.add(values[a], values[b], -1)
            if lit < 0:
                require(self.witness(lit) in names, 'missing inverse witness')
                value = ar.add(ar.mul(value, {(names[self.witness(lit)],): 1}), {(): 1}, -1)
            release(a); release(b)
            yield value

    def choice(self, lit):
        g = self.g; a, b = g.nodes[abs(lit)][1]; binder = f'{g.prefix}bound{abs(lit)}'
        return f'(choice (({binder} {sort_text(g.p)})) (= (ff.mul {binder} (ff.add {g.ref(a)} (ff.neg {g.ref(b)}))) (as ff1 {sort_text(g.p)})))'

    def original_variables(self, variables):
        mapping = {self.variable(i): self.g.ref(i) for i in self.used if self.g.nodes[i][0] in ('var', 'ite')}
        mapping.update({self.witness(x): self.choice(x) for x in self.equations if x < 0})
        return [mapping[x] for x in variables]


def compact(g, literals, dag):
    # Producer-side pruning is untrusted. Validate its syntax here; the full
    # algebra and original-input binding are checked by verify_export before
    # publishing, and independently again by check_bundle on the stored bundle.
    cert = fc.read_certificate(dag)
    require(len(cert[':inputs']) == len(literals), 'input count mismatch')
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
    return core, result


def produce(original, z3, timeout, backend="auto", boolean_backend="auto", field_session=None):
    require(backend in ("auto", "scalar", "f4", "native"), "invalid certificate backend")
    require(boolean_backend in ("auto", "native", "incremental", "integrated", "ranges", "circuits", "legacy"), "invalid Boolean backend")
    import ff_proof_pipeline as pp
    start = time.monotonic(); g = Graph(original, ranges=boolean_backend in ("ranges", "circuits"), compounds=boolean_backend == "circuits"); base = Clauses(g)
    if boolean_backend in ("ranges", "circuits"):
        require(backend == "native", "range search requires native polynomial certificates")
        import ff_range_proof
        return ff_range_proof.produce(g, base, z3, start, timeout, version=4 if boolean_backend == "circuits" else 3)
    if boolean_backend == "integrated":
        require(backend == "native", 'integrated search requires native polynomial certificates')
        return produce_integrated(g, base, z3, start, timeout)
    native = boolean_backend == "native" or (boolean_backend == "auto" and backend == "native")
    incremental = boolean_backend == "incremental" or (boolean_backend == "auto" and backend == "native" and os.name == 'posix')
    if field_session is None: field_session = incremental and backend == 'native'
    search = (IncrementalSearch(base.clauses, z3, start + timeout) if incremental else
              NativeSearch(base.clauses, z3, start + timeout) if native else Search(base.clauses))
    field = None
    try:
        if field_session: field = pp.FieldSession(z3)
        return produce_search(g, base, search, z3, start, timeout, backend, field)
    finally:
        if field is not None: field.close()
        if isinstance(search, NativeSearch): search.close()




def produce_integrated(g, base, z3, start, timeout):
    """Native SAT extension; all returned evidence remains untrusted here."""
    import ff_proof_pipeline as pp
    variables = sorted({abs(x) for c in base.clauses for x in c})
    atoms = [v for v in variables if g.field_atom(v)]
    search = WatchedSearch(base.clauses, z3, start + timeout)
    if not atoms:
        sat, result = search.search()
        require(not sat, 'Boolean formula has no recorded contradiction')
        return finish_proof(base, search, result)
    # Register both polarities once. The negative equation uses the same fresh
    # inverse witness as Case and the independent original-input binding checker.
    positive, negative = Case(g, atoms), Case(g, [-v for v in atoms])
    lines = ['(set-logic ALL)']
    lines += [line for line in negative.normalized().splitlines() if not line.startswith(('(set-logic ', '(assert '))]
    lines += [f'(declare-const b{v} Bool)' for v in variables]
    for v in atoms:
        lines += [f'(assert (= b{v} {positive.eq_text(v)}))',
                  f'(assert (= (not b{v}) {negative.eq_text(-v)}))']
    for c in base.clauses:
        terms = [f'b{x}' if x > 0 else f'(not b{-x})' for x in c]
        body = 'false' if not terms else terms[0] if len(terms) == 1 else '(or ' + ' '.join(terms) + ')'
        lines.append(f'(assert {body})')
    remaining = timeout - (time.monotonic() - start)
    require(remaining > 0, 'Boolean pipeline timeout')
    lines.append(f'(ff-integrated-certify :timeout {max(1, int(remaining * 900))})')
    text = '\n'.join(lines) + '\n'
    require(len(text.encode()) <= 32*1024*1024, 'integrated input size limit')
    output = pp.run([str(z3), '-in'], remaining, text)['stdout']
    return consume_integrated(g, base, search, variables, output)


def consume_integrated(g, base, search, variables, output):
    objects = fc.parse(output)
    require(len(objects) == 1 and isinstance(objects[0], list), 'invalid integrated response')
    obj = objects[0]
    require(len(obj) == 9 and obj[0] == 'ff-integrated-result' and
            obj[1::2] == [':status', ':variables', ':lemmas', ':clauses'] and obj[2] == 'unsat',
            'native integrated proof unavailable: ' + output[:160])
    native_names, lemmas, trace = obj[4], obj[6], obj[8]
    expected = {f'b{v}': v for v in variables}
    require(isinstance(native_names, list) and len(native_names) <= 100001 and
            all(isinstance(x, str) for x in native_names), 'invalid integrated variable list')
    # A SAT-internal leading slot, if present, has no formula binding and may
    # never occur in a field lemma or a replayed SAT inference.
    named = [x for x in native_names if x != '_']
    require(len(set(named)) == len(named) and set(named) == set(expected) and
            all(x != '_' or i == 0 for i, x in enumerate(native_names)), 'integrated variable binding mismatch')
    mapping = {i+1: expected[x] for i, x in enumerate(native_names) if x != '_'}
    require(isinstance(lemmas, list) and len(lemmas) <= MAX_LEMMAS, 'integrated field lemma limit')
    for raw in lemmas:
        require(isinstance(raw, list), 'malformed integrated lemma')
        attrs = fc.attributes(raw, {':literals', ':certificate'})
        require(isinstance(attrs[':literals'], list), 'malformed integrated premise list')
        literals = []
        for atom in attrs[':literals']:
            require(isinstance(atom, str) and atom.lstrip('-').isdigit(), 'invalid integrated literal')
            lit = int(atom)
            require(abs(lit) in mapping, 'unbound integrated premise')
            literals.append(mapping[abs(lit)] * (1 if lit > 0 else -1))
        Case(g, literals)  # Reject duplicate/opposite and non-field premises.
        dag = fc.try_balance_certificate(fc.sexpr(attrs[':certificate']))
        core, dag = compact(g, literals, dag)
        search.append(clause(-x for x in core), dict(rule='field', literals=core, certificate=dag))
    # Field lemmas are globally valid conditionals after independent checking;
    # their search-time order does not make them additional trusted assumptions.
    sat, result = search.replay_trace(mapping, trace)
    require(not sat, 'missing integrated Boolean contradiction')
    return finish_proof(base, search, result)


def finish_proof(base, search, result):
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

def produce_search(g, base, search, z3, start, timeout, backend, field=None):
    import ff_proof_pipeline as pp
    lemmas = 0
    while True:
        require(time.monotonic() - start < timeout, 'Boolean pipeline timeout')
        sat, result = search.search()
        if not sat:
            return finish_proof(base, search, result)
        require(lemmas < MAX_LEMMAS, 'field lemma count limit')
        literals = sorted([i if v else -i for i, v in result.items() if g.field_atom(i)], key=abs)
        require(literals, 'no field conflict (possibly satisfiable)')
        case = Case(g, literals)
        remaining = timeout - (time.monotonic() - start); require(remaining > 0, 'Boolean pipeline timeout')
        output = (field.query(case.normalized(), start + timeout, backend) if field is not None else
                  pp.run([str(z3), '-in'], remaining, case.normalized() + pp.certificate_command(remaining, backend))['stdout'])
        require(output.startswith('(ff-certificate\n'), 'field certificate unavailable: ' + output[:300].strip())
        if backend == 'native': output = fc.try_balance_certificate(output)
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
            elif src[0] == 'cut':
                name = self.step([g.ref(src[1])], 'refl')
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
        cert, pac = pp.verified_pac(case, dag)
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
        self.step([], 'ff_pac', [conversion], [pac])
        discharged = [f'(not {g.literal(x)})' for x in literals] + ['false']
        self.step(discharged, 'subproof', name=lemma, discharge=assumptions)
        final = self.step([g.literal(-x) for x in literals], 'resolution', [lemma, self.false])
        return final, case.normalized(), pac


def verify_export(original, proof):
    require(isinstance(proof, dict) and set(proof) == {'version', 'records', 'root'} and type(proof['version']) is int and proof['version'] in (2, 3, 4), 'unknown Boolean certificate schema')
    require(isinstance(proof['records'], list) and len(proof['records']) <= MAX_RECORDS, 'record limit')
    g = Graph(original, ranges=proof['version'] in (3,4), compounds=proof['version'] == 4); base = Clauses(g); clauses = list(base.clauses); writer = Writer(g); writer.base(base)
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


def produce_bundle(original, directory, z3, timeout, backend="auto", boolean_backend="auto", field_session=None):
    proof = produce(original, z3, timeout, backend, boolean_backend, field_session)
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
