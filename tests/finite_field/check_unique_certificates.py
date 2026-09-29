#!/usr/bin/env python3
"""Replay ff-unique derivations as independently checked steps.

Runs the reference uniqueness propagation with Boolean splits (the algorithm
of src/tactic/arith/ff_unique_tactic.cpp), records every derived equality,
value, split and branch closure together with the asserted constraints and
earlier facts it uses, and asks an independent solver to confirm each step
as an unsatisfiable local query (premises, facts, negated conclusion).

Usage: check_unique_certificates.py --solver /path/to/cvc5 FILE.smt2 ...
"""
import argparse, subprocess

import sys, time
from collections import defaultdict
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def load(path):
    src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ff_unique_reference.py')).read()
    code = src.replace("    decided = [canon(f) == () for f in neqs]",
                       "    global DBG\n    DBG=(eqs,neqs,bools,p)\n    decided = [canon(f) == () for f in neqs]")
    ns = {}
    exec(compile(code, 'x', 'exec'), ns)
    ns['main'](path)
    return ns['DBG']


class State:
    def __init__(s, p, parent=None, val=None, facts=None):
        s.p = p
        s.parent = dict(parent or {})
        s.val = dict(val or {})
        s.facts = list(facts or [])   # ('eq', a, b) or ('val', a, k): the branch's derived facts
        s.steps = None                # when certifying: list of (facts_len, premises, conclusion)

    def find(s, v):
        par = s.parent
        par.setdefault(v, v)
        while par[v] != v:
            par[v] = par[par[v]]
            v = par[v]
        return v

    def union(s, a, b, prem=()):
        oa, ob = a, b
        a, b = s.find(a), s.find(b)
        if a == b:
            return 'same'
        va, vb = s.val.get(a), s.val.get(b)
        if va is not None and vb is not None and va != vb:
            if s.steps is not None:
                s.steps.append((tuple(s.facts), tuple(prem), ('false',)))
            return 'conflict'
        if s.steps is not None:
            s.steps.append((tuple(s.facts), tuple(prem), ('eq', oa, ob)))
        s.facts.append(('eq', oa, ob))
        lo, hi = min(a, b), max(a, b)
        s.parent[hi] = lo
        v = va if va is not None else vb
        if v is not None:
            s.val[lo] = v
        s.val.pop(hi, None)
        return 'merged'

    def setval(s, a, v, prem=(), assumption=False):
        oa = a
        a = s.find(a)
        old = s.val.get(a)
        if old is not None:
            if old != v and s.steps is not None and not assumption:
                s.steps.append((tuple(s.facts), tuple(prem), ('false',)))
            return 'same' if old == v else 'conflict'
        if s.steps is not None and not assumption:
            s.steps.append((tuple(s.facts), tuple(prem), ('val', oa, v)))
        s.facts.append(('val', oa, v))
        s.val[a] = v
        return 'merged'

    def canon(s, f):
        p = s.p
        r = {}
        for m, c in f.items():
            coeff = c
            mm = []
            for v in m:
                rv = s.find(v)
                if rv in s.val:
                    coeff = coeff * s.val[rv] % p
                else:
                    mm.append(rv)
            if coeff == 0:
                continue
            mm = tuple(sorted(mm))
            x = (r.get(mm, 0) + coeff) % p
            if x:
                r[mm] = x
            else:
                r.pop(mm, None)
        return r


def propagate(st, eqs, neqs, bools):
    p = st.p
    inv = lambda a: pow(a, p - 2, p)
    while True:
        changed = False
        defs = {}
        # is-zero gadgets: (y - d)*S = 0 with S free of y and d constant.
        zs = defaultdict(dict)
        for j, f in enumerate(eqs):
            g = st.canon(f)
            if not g or () in g and len(g) == 1:
                continue
            ys = set()
            for m in g:
                cnt = defaultdict(int)
                for v in m:
                    cnt[v] += 1
                ys |= {v for v, k in cnt.items() if k == 1}
            for y in ys:
                S, R, ok = {}, {}, True
                for m, c in g.items():
                    k = m.count(y)
                    if k == 1:
                        l = list(m); l.remove(y); S[tuple(l)] = c
                    elif k == 0:
                        R[m] = c
                    else:
                        ok = False; break
                if not ok or not S or any(y in m for m in S):
                    continue
                lead = max(S, key=lambda k: (len(k), k))
                if R:
                    if set(R) != set(S):
                        continue
                    lam = R[lead] * inv(S[lead]) % p
                    if any((R[m] - lam * S[m]) % p for m in S):
                        continue
                    d = (-lam) % p
                else:
                    d = 0
                ic = inv(S[lead])
                Sk = tuple(sorted((m, c * ic % p) for m, c in S.items()))
                zs[y].setdefault(Sk, (d, j))
        for i, f in enumerate(eqs):
            g = st.canon(f)
            if not g:
                continue
            if len(g) == 1 and () in g:
                if st.steps is not None:
                    st.steps.append((tuple(st.facts), (('e', i),), ('false',)))
                return 'conflict'
            occ = defaultdict(int)
            for m in g:
                for v in set(m):
                    occ[v] += 1
            # one-variable constraints over a Boolean class: b*b-b is trivial;
            # other univariate constraints with a single linear term fix a value.
            for m, c in g.items():
                if len(m) != 1 or occ[m[0]] != 1:
                    continue
                y = m[0]
                ia = inv(c)
                rest = {mm: (-cc * ia) % p for mm, cc in g.items() if mm != m}
                if not rest or list(rest) == [()]:
                    r = st.setval(y, rest.get((), 0), (('e', i),))
                    if r == 'conflict':
                        return 'conflict'
                    changed |= r == 'merged'
                    continue
                if len(rest) == 1:
                    (mm, cc), = rest.items()
                    if len(mm) == 1 and cc == 1:
                        r = st.union(y, mm[0], (('e', i),))
                        if r == 'conflict':
                            return 'conflict'
                        changed |= r == 'merged'
                        continue
                # y = c - z*S with y*S = 0 known: y = c*[S == 0], a function of S.
                if st.find(y) in zs:
                    c0 = rest.get((), 0)
                    rp = {mm: cc for mm, cc in rest.items() if mm != ()}
                    zcands = None
                    for mm in rp:
                        cnt = defaultdict(int)
                        for v in mm:
                            cnt[v] += 1
                        ones = {v for v, k in cnt.items() if k == 1}
                        zcands = ones if zcands is None else zcands & ones
                    hit = False
                    for z in zcands or ():
                        S = {}
                        for mm, cc in rp.items():
                            l = list(mm); l.remove(z)
                            S[tuple(l)] = (-cc) % p
                        if not S:
                            continue
                        ic = inv(S[max(S, key=lambda k: (len(k), k))])
                        Sk = tuple(sorted((mm, cc * ic % p) for mm, cc in S.items()))
                        if Sk in zs[st.find(y)]:
                            key = ('iz', c0, zs[st.find(y)][Sk][0], Sk)
                            if key in defs:
                                j0, j1 = defs[key][2], zs[st.find(y)][Sk][1]
                                r = st.union(defs[key][0], y, (('e', defs[key][1]), ('e', j0), ('e', i), ('e', j1)))
                                if r == 'conflict':
                                    return 'conflict'
                                changed |= r == 'merged'
                            else:
                                defs[key] = (y, i, zs[st.find(y)][Sk][1])
                            hit = True
                            break
                    if hit:
                        continue
                key = ('lin', tuple(sorted(rest.items())))
                if key in defs:
                    r = st.union(defs[key][0], y, (('e', defs[key][1]), ('e', i)))
                    if r == 'conflict':
                        return 'conflict'
                    changed |= r == 'merged'
                else:
                    defs[key] = (y, i)
            # Boolean domain: b*(b-1) with b Boolean already known to the class
            bset = {st.find(b) for b in bools}
            bterms = [(m[0], c) for m, c in g.items() if len(m) == 1 and m[0] in bset and occ[m[0]] == 1]
            if len(bterms) >= 2:
                for _, c0 in bterms[:3]:
                    ic = inv(c0)
                    exps = {}
                    ok = True
                    for b, c in bterms:
                        w = c * ic % p
                        if w & (w - 1) == 0:
                            e = w.bit_length() - 1
                            if e in exps:
                                ok = False
                                break
                            exps[e] = b
                    if not ok or not exps or (1 << (max(exps) + 1)) > p:
                        continue
                    used = set(exps.values())
                    rest = {mm: (-cc * ic) % p for mm, cc in g.items() if not (len(mm) == 1 and mm[0] in used)}
                    if not rest or list(rest) == [()]:
                        k = rest.get((), 0)
                        if any((k >> e) & 1 and e not in exps for e in range(k.bit_length())):
                            if st.steps is not None:
                                st.steps.append((tuple(st.facts), (('e', i),), ('false',)))
                            return 'conflict'
                        for e, b in exps.items():
                            r = st.setval(b, (k >> e) & 1, (('e', i),))
                            if r == 'conflict':
                                return 'conflict'
                            changed |= r == 'merged'
                        continue
                    base = tuple(sorted(rest.items()))
                    for e, b in exps.items():
                        key = ('bit', e, base)
                        if key in defs:
                            r = st.union(defs[key][0], b, (('e', defs[key][1]), ('e', i)))
                            if r == 'conflict':
                                return 'conflict'
                            changed |= r == 'merged'
                        else:
                            defs[key] = (b, i)
                    break
        for j, f in enumerate(neqs):
            if not st.canon(f):
                if st.steps is not None:
                    st.steps.append((tuple(st.facts), (('n', j),), ('false',)))
                return 'conflict'
        if not changed:
            return 'open'


def search(st, eqs, neqs, bools, depth, budget, stats):
    stats['nodes'] += 1
    if stats['nodes'] > budget:
        raise TimeoutError()
    r = propagate(st, eqs, neqs, bools)
    if r == 'conflict':
        return True
    if depth == 0:
        return False
    # candidate split variables: Boolean classes without value occurring in
    # constraints that still contain two distinct classes (not fully merged)
    score = defaultdict(int)
    bset = {st.find(b) for b in bools}
    for f in eqs:
        g = st.canon(f)
        vs = {v for m in g for v in m}
        for v in vs:
            if v in bset and v not in st.val:
                score[v] += 1
    if not score:
        return False
    v = max(score, key=lambda k: score[k])
    for value in (0, 1):
        child = State(st.p, st.parent, st.val, st.facts)
        child.steps = st.steps
        if st.steps is not None and value == 0:
            st.steps.append((tuple(st.facts), (('bools',),), ('split', v)))
        if child.setval(v, value, assumption=True) == 'conflict':
            continue
        if not search(child, eqs, neqs, bools, depth - 1, budget, stats):
            return False
    return True


def main(path, depth=12, budget=20000, certify=None):
    eqs, neqs, bools, p = load(path)
    st = State(p)
    if certify is not None:
        st.steps = certify
    stats = {'nodes': 0}
    t = time.time()
    try:
        res = search(st, eqs, neqs, bools, depth, budget, stats)
        out = 'unsat' if res else 'open'
    except TimeoutError:
        out = 'budget'
    return out, stats['nodes'], round(time.time() - t, 3)




def poly_smt(f):
    parts = []
    for m, c in f.items():
        if not m:
            parts.append(f'(as ff{c} F)')
        else:
            parts.append(f'(ff.mul (as ff{c} F) {" ".join(m)})' if c != 1 else (m[0] if len(m) == 1 else f'(ff.mul {" ".join(m)})'))
    if not parts:
        return '(as ff0 F)'
    return parts[0] if len(parts) == 1 else f'(ff.add {" ".join(parts)})'

def check(path, solver):
    steps = []
    res = main(path, depth=16, budget=50000, certify=steps)
    if res[0] != 'unsat':
        print(path, res); return
    eqs, neqs, bools, p = load(path)
    names = sorted({v for f in eqs + neqs for m in f for v in m})
    head = [f'(set-logic QF_FF)', f'(define-sort F () (_ FiniteField {p}))'] + [f'(declare-const {v} F)' for v in names]
    boolc = [f for f in eqs if len(f) == 2 and any(len(m) == 2 and m[0] == m[1] and m[0] in bools for m in f)]
    bad = 0
    for facts, prem, concl in steps:
        L = list(head)
        for kind, *rest in prem:
            if kind == 'e':
                L.append(f'(assert (= {poly_smt(eqs[rest[0]])} (as ff0 F)))')
            elif kind == 'n':
                L.append(f'(assert (not (= {poly_smt(neqs[rest[0]])} (as ff0 F))))')
            elif kind == 'bools':
                L += [f'(assert (= {poly_smt(f)} (as ff0 F)))' for f in boolc]
        for fct in facts:
            if fct[0] == 'eq':
                L.append(f'(assert (= {fct[1]} {fct[2]}))')
            else:
                L.append(f'(assert (= {fct[1]} (as ff{fct[2]} F)))')
        if concl[0] == 'eq':
            L.append(f'(assert (not (= {concl[1]} {concl[2]})))')
        elif concl[0] == 'val':
            L.append(f'(assert (not (= {concl[1]} (as ff{concl[2]} F))))')
        elif concl[0] == 'split':
            v = concl[1]
            L.append(f'(assert (not (or (= {v} (as ff0 F)) (= {v} (as ff1 F)))))')
        L.append('(check-sat)')
        r = subprocess.run(solver + ['--lang=smt2', '--tlimit=20000'] if 'cvc5' in solver[0] else solver + ['-in', '-T:20'], input='\n'.join(L), capture_output=True, text=True).stdout.strip()
        if r != 'unsat':
            bad += 1
            print('STEP NOT CHECKED', r, prem, concl)
    print(path.split('/')[-1], res, 'steps', len(steps), 'unchecked', bad, flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--solver', required=True, help='cvc5 or z3 binary used as the independent checker')
    ap.add_argument('files', nargs='+')
    a = ap.parse_args()
    for pth in a.files:
        check(pth, [a.solver])
