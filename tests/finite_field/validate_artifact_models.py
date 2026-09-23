#!/usr/bin/env python3
"""Independently evaluate original SAT assertions using Python arithmetic.

Models are obtained in a separate untimed run. A failed model retrieval or an
unsupported construct is reported explicitly and is never called a valid model.
"""
import argparse
import collections
import dataclasses
import hashlib
import json
import math
import re
from pathlib import Path
from benchmark_artifacts import prepare, run
from benchmark_public_ff import sexprs


@dataclasses.dataclass(frozen=True)
class BV:
    value: int
    width: int

    def __post_init__(self):
        object.__setattr__(self, 'value', self.value % (1 << self.width))

    def signed(self):
        return self.value if self.value < (1 << (self.width-1)) else self.value-(1 << self.width)


def evaluate(node, env, p):
    if isinstance(node, str):
        if node == 'true': return True
        if node == 'false': return False
        if node.startswith('#f'): return int(node[2:].split('m')[0]) % p
        if node.startswith('#b'): return BV(int(node[2:], 2), len(node)-2)
        if node.startswith('#x'): return BV(int(node[2:], 16), 4*(len(node)-2))
        return env[node]
    if node[0] == 'let':
        env = env.copy()
        while isinstance(node, list) and node[0] == 'let':
            # SMT-LIB let bindings are simultaneous, not sequential.
            env.update({name: evaluate(value, env, p) for name, value in node[1]})
            node = node[2]
        return evaluate(node, env, p)
    if node[0] == 'as': return int(node[1][2:]) % p
    if node[0] == '_' and node[1].startswith('bv'): return BV(int(node[1][2:]), int(node[2]))
    op = node[0]
    if op == 'ite': return evaluate(node[2] if evaluate(node[1], env, p) else node[3], env, p)
    v = [evaluate(x, env, p) for x in node[1:]]
    if isinstance(op, list):
        assert op[0] == '_'
        a = v[0]
        if op[1] == 'extract': return BV(a.value >> int(op[3]), int(op[2])-int(op[3])+1)
        if op[1] == 'zero_extend': return BV(a.value, a.width+int(op[2]))
        if op[1] == 'sign_extend': return BV(a.signed(), a.width+int(op[2]))
        raise ValueError(('unsupported indexed operator', op))
    if op == 'ff.add': return sum(v) % p
    if op == 'ff.mul': return math.prod(v) % p
    if op == 'ff.neg': return -v[0] % p
    if op == 'ff.bitsum': return sum((1 << i)*a for i, a in enumerate(v)) % p
    if op == '=': return all(a == v[0] for a in v[1:])
    if op == 'distinct': return len(set(v)) == len(v)
    if op == 'not': return not v[0]
    if op == 'and': return all(v)
    if op == 'or': return any(v)
    if op == '=>': return not all(v[:-1]) or v[-1]
    if op == 'xor': return bool(sum(v) % 2)
    if op == 'concat':
        a, b = v
        return BV((a.value << b.width) | b.value, a.width+b.width)
    if op.startswith('bv'):
        a = v[0]; w = a.width; x = a.value
        if op == 'bvnot': return BV(~x, w)
        if op == 'bvneg': return BV(-x, w)
        b = v[1]; y = b.value
        assert w == b.width
        if op in ['bvult','bvule','bvugt','bvuge','bvslt','bvsle','bvsgt','bvsge']:
            if op[2] == 's': x, y = a.signed(), b.signed()
            return {'lt': x < y, 'le': x <= y, 'gt': x > y, 'ge': x >= y}[op[3:]]
        if op == 'bvadd': return BV(x+y, w)
        if op == 'bvsub': return BV(x-y, w)
        if op == 'bvmul': return BV(x*y, w)
        if op == 'bvand': return BV(x & y, w)
        if op == 'bvor': return BV(x | y, w)
        if op == 'bvxor': return BV(x ^ y, w)
        if op == 'bvudiv': return BV(x//y if y else -1, w)
        if op == 'bvurem': return BV(x % y if y else x, w)
        # Bound shifts before Python computes a potentially enormous integer.
        if op == 'bvshl': return BV(x << y if y < w else 0, w)
        if op == 'bvlshr': return BV(x >> y if y < w else 0, w)
        if op == 'bvashr': return BV(a.signed() >> min(y, w), w)
    raise ValueError(('unsupported operator', op))


def validate(original, model):
    commands = sexprs(original)
    primes = {int(p) for p in re.findall(r'\(_\s+FiniteField\s+(\d+)\)', original)}
    assert len(primes) == 1, 'checker supports one prime per input'
    prime = primes.pop()
    names = [c[1] for c in commands if c[0] == 'declare-const' or (c[0] == 'declare-fun' and c[2] == [])]
    nameset = set(names)
    assignments = next(c for c in sexprs(model) if isinstance(c, list) and len(c) == len(names)
                       and all(isinstance(a, list) and len(a) == 2 and a[0] in nameset for a in c)) if names else []
    env = {n: evaluate(value, {}, prime) for n, value in assignments}
    assert set(env) == nameset, 'incomplete model'
    count = 0
    for c in commands:
        if c[0] == 'assert':
            assert evaluate(c[1], env, prime) is True, f'false original assertion {count}'
            count += 1
    return count


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--corpus', type=Path, required=True)
    ap.add_argument('--results', type=Path, required=True)
    ap.add_argument('--timeout', type=float, default=30)
    ap.add_argument('--run-log', default='runs.jsonl', help='primary runs or a separate follow-up log')
    args = ap.parse_args()
    path = args.results/('models.jsonl' if args.run_log=='runs.jsonl' else 'models-'+Path(args.run_log).stem+'.jsonl')
    done = {(r['sha256'], r['solver']) for r in map(json.loads, path.read_text().splitlines())} if path.exists() else set()
    runs = [json.loads(l) for l in (args.results/args.run_log).read_text().splitlines()]
    commands = {'z3': [str((args.results/'binaries/z3').resolve()), '-in'],
                'cvc5': [str((args.results/'binaries/cvc5').resolve()), '--lang=smt2'],
                'cvc5_split': [str((args.results/'binaries/cvc5').resolve()), '--lang=smt2', '--ff-solver=split']}
    with path.open('a', buffering=1) as output:
        for r in runs:
            key = r['sha256'], r['solver']
            if r['result'] != 'sat' or key in done: continue
            original = (args.corpus/'inputs'/(key[0]+'.smt2')).read_text()
            assert hashlib.sha256(original.encode()).hexdigest() == key[0]
            cmds = sexprs(original)
            names = [c[1] for c in cmds if c[0] == 'declare-const' or (c[0] == 'declare-fun' and c[2] == [])]
            smt = '(set-option :produce-models true)\n'+prepare(original, solver=key[1])
            if names: smt += '\n(get-value ('+' '.join(names)+'))\n'
            model = run(dict(command=commands[key[1]], smt=smt, timeout=args.timeout, checks=1, output_limit=None))
            row = dict(sha256=key[0], solver=key[1], model_result=model['result'])
            if model['result'] == 'sat':
                try:
                    row['assertions'] = validate(original, model['stdout']); row['validation'] = 'valid'
                except Exception as e:
                    row['validation'] = 'check-failed'; row['detail'] = repr(e); row['model'] = model['stdout']
            else:
                row['validation'] = 'retrieval-failed'; row['detail'] = model
            output.write(json.dumps(row)+'\n')
            done.add(key)
            if row['validation'] != 'valid': print(row, flush=True)
    print(collections.Counter(json.loads(l)['validation'] for l in path.read_text().splitlines()))


if __name__ == '__main__': main()
