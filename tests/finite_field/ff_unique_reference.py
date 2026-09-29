#!/usr/bin/env python3
"""Reference implementation of uniqueness propagation (functional-dependency congruence) for QF_FF.

Reads an SMT-LIB QF_FF file, flattens the top-level conjunction, turns field
equalities into polynomials, and saturates:
  * union-find over variables, seeded with asserted equalities v = w;
  * a constraint a*y + r = 0 (y occurring once, linearly, with constant a != 0)
    defines y := -r/a; two definitions with the same canonical right-hand side
    (variables replaced by class representatives) merge their y;
  * a bit decomposition sum c*2^e_i*b_i + r = 0 over Boolean b_i (b*b = b), with
    distinct e_i and 2^(max e + 1) <= p, defines each b_i := bit_{e_i}(-r/c).
Reports whether a top-level disequality (not (= s t)) becomes s ~ t (UNSAT).
"""
import sys, re, itertools
from collections import defaultdict

sys.setrecursionlimit(1000000)


def tokenize(text):
    return re.findall(r'\(|\)|[^\s()]+', text)


def parse(tokens):
    stack = [[]]
    for t in tokens:
        if t == '(':
            stack.append([])
        elif t == ')':
            x = stack.pop()
            stack[-1].append(x)
        else:
            stack[-1].append(t)
    return stack[0]


class Budget(Exception):
    pass


MAXTERMS = 256


def padd(a, b, p, s=1):
    r = dict(a)
    for m, c in b.items():
        v = (r.get(m, 0) + s * c) % p
        if v:
            r[m] = v
        else:
            r.pop(m, None)
    return r


def pmul(a, b, p):
    r = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(sorted(m1 + m2))
            v = (r.get(m, 0) + c1 * c2) % p
            if v:
                r[m] = v
            else:
                r.pop(m, None)
    if len(r) > MAXTERMS:
        raise Budget()
    return r


def main(path):
    text = open(path).read()
    exprs = parse(tokenize(text))
    p = None
    sorts = {}
    asserts = []
    for e in exprs:
        if e[0] == 'define-sort':
            p = int(e[3][2])
        elif e[0] == 'declare-fun':
            pass
        elif e[0] == 'assert':
            asserts.append(e[1])
    env_stack = []

    # expand lets lazily with memo on (id)
    def ev(x, env):
        # returns ('bool', expr-list-form) or polynomial dict
        while isinstance(x, list) and x and x[0] == 'let':
            env = dict(env)
            for name, val in x[1]:
                env[name] = (val, env_snapshot(env))
            x = x[2]
        return x, env

    def env_snapshot(env):
        return env

    memo = {}

    def poly(x, env):
        if isinstance(x, str):
            if x in env:
                val, venv = env[x]
                key = id(val)
                if key in memo:
                    return memo[key]
                r = poly(val, venv)
                memo[key] = r
                return r
            if x.startswith('ff') and x[2:].lstrip('-').isdigit():
                v = int(x[2:]) % p
                return {(): v} if v else {}
            return {(x,): 1}
        if x[0] == 'as':
            v = int(x[1][2:]) % p
            return {(): v} if v else {}
        if x[0] == 'let':
            y, env2 = ev(x, env)
            return poly(y, env2)
        op = x[0]
        args = [poly(a, env) for a in x[1:]]
        if op == 'ff.add':
            r = {}
            for a in args:
                r = padd(r, a, p)
            return r
        if op == 'ff.mul':
            r = {(): 1}
            for a in args:
                r = pmul(r, a, p)
            return r
        if op == 'ff.neg':
            return {m: (-c) % p for m, c in args[0].items()}
        raise ValueError(op)

    eqs, neqs = [], []
    skipped = 0

    def boolean(x, env, positive=True):
        nonlocal skipped
        if isinstance(x, str):
            if x in env:
                val, venv = env[x]
                return boolean(val, venv, positive)
            return
        if x[0] == 'let':
            y, env2 = ev(x, env)
            return boolean(y, env2, positive)
        if x[0] == 'and' and positive:
            for a in x[1:]:
                boolean(a, env, True)
            return
        if x[0] == 'not':
            if positive:
                boolean(x[1], env, False)
            return
        if x[0] == '=':
            try:
                a = poly(x[1], env)
                b = poly(x[2], env)
            except Budget:
                skipped += 1
                return
            except (ValueError, KeyError, TypeError):
                skipped += 1
                return
            d = padd(a, b, p, -1)
            (eqs if positive else neqs).append(d)
            return
        skipped += 1

    for a in asserts:
        boolean(a, {}, True)

    # union-find
    parent = {}

    def find(v):
        parent.setdefault(v, v)
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    def union(a, b):
        a, b = find(a), find(b)
        if a == b:
            return False
        parent[max(a, b)] = min(a, b)
        return True

    bools = set()
    for f in eqs:
        # b*b - b
        if len(f) == 2:
            ms = sorted(f.items(), key=lambda t: -len(t[0]))
            (m2, c2), (m1, c1) = ms
            if len(m2) == 2 and m2[0] == m2[1] and m1 == (m2[0],) and (c1 + c2) % p == 0:
                bools.add(m2[0])

    def canon(poly_terms):
        r = {}
        for m, c in poly_terms.items():
            mm = tuple(sorted(find(v) for v in m))
            v = (r.get(mm, 0) + c) % p
            if v:
                r[mm] = v
            else:
                r.pop(mm, None)
        return tuple(sorted(r.items()))

    inv = lambda a: pow(a, p - 2, p)
    rounds = 0
    changed = True
    while changed:
        changed = False
        rounds += 1
        defs = {}
        for f in eqs:
            # linear definitions
            occ = defaultdict(int)
            for m in f:
                for v in set(m):
                    occ[v] += 1
            for m, c in f.items():
                if len(m) != 1:
                    continue
                y = m[0]
                if occ[y] != 1:
                    continue
                ia = inv(c)
                rest = {mm: (-cc * ia) % p for mm, cc in f.items() if mm != m}
                cr = canon(rest)
                if len(cr) == 1 and len(cr[0][0]) == 1 and cr[0][1] == 1:
                    if union(cr[0][0][0], y):
                        changed = True
                    continue
                key = ('lin', cr)
                if key in defs:
                    if union(defs[key], y):
                        changed = True
                else:
                    defs[key] = find(y)
            # bit decompositions
            bterms = [(m[0], c) for m, c in f.items() if len(m) == 1 and m[0] in bools]
            if len(bterms) >= 2:
                for _, c0 in bterms[:3]:
                    ic = inv(c0)
                    exps = {}
                    ok = True
                    for b, c in bterms:
                        w = (c * ic) % p
                        if w & (w - 1) == 0 and w < p:
                            e = w.bit_length() - 1
                            if e in exps:
                                ok = False
                                break
                            exps[e] = b
                    if not ok or not exps or (1 << (max(exps) + 1)) > p:
                        continue
                    used = set(exps.values())
                    rest = {mm: (-cc * ic) % p for mm, cc in f.items() if not (len(mm) == 1 and mm[0] in used)}
                    base = canon(rest)
                    for e, b in exps.items():
                        key = ('bit', e, base)
                        if key in defs:
                            if union(defs[key], b):
                                changed = True
                        else:
                            defs[key] = find(b)
                    break
    decided = [canon(f) == () for f in neqs]
    return dict(eqs=len(eqs), neqs=len(neqs), skipped=skipped, rounds=rounds, bools=len(bools),
                unsat=any(decided), classes=len({find(v) for v in parent}), vars=len(parent))


if __name__ == '__main__':
    for path in sys.argv[1:]:
        try:
            r = main(path)
        except RecursionError:
            r = 'recursion'
        print(path.split('/')[-1], r, flush=True)
