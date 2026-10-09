#!/usr/bin/env python3
"""Bounded Z3 -> Alethe/PAC -> Carcara/FFPacheck pipeline.

The original input, checked DAG and exact exported bytes are checked together.
External checker acceptance alone is insufficient: the pinned Carcara ff_pac
bridge does not bind PAC axioms to its premise. See QF_FF_PROOF_PIPELINE.md.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

import ff_certificate as fc

CARCARA_REVISION = '6e005a9b0093c9df7500cc11063f9c2fdc3afd7a'
FFPACHECK_REVISION = '04fb1683bd694730ec186047f1f1a63f13ba2ada'
LIMIT = 32 * 1024 * 1024


def numeral(c, p):
    return f'#f{c % p}m{p}'


class LiteralProblem(fc.Problem):
    """A small trusted bridge for conjunctions of positive/negative FF equalities.

    For d != 0 in a field, there exists w with d*w - 1 = 0, and conversely.
    Fresh witnesses therefore preserve satisfiability. In Alethe each witness
    becomes the artifact's explicit Hilbert-choice term, checked by ff_diseq.
    No Boolean case splitting or solver preprocessing is assumed here.
    """
    def __init__(self, text):
        self.literals, self.witnesses = [], {}
        # Reserve every symbol, including names declared later and let binders.
        self.reserved = set()
        pending = fc.parse(text)
        while pending:
            x = pending.pop()
            if isinstance(x, list):
                pending.extend(x)
            elif not x.startswith('"'):
                self.reserved.add(fc.symbol(x))
        super().__init__(text)

    def field_of(self, e):
        if isinstance(e, str):
            if e.startswith('#f'):
                return int(e.rsplit('m', 1)[1])
            fc.require(fc.symbol(e) in self.declarations, 'unknown field constant')
            return self.declarations[fc.symbol(e)][1]
        if e[0] == 'as':
            return self.sort(e[2])
        fc.require(e[0] in ('ff.add', 'ff.mul', 'ff.neg', 'ff.bitsum') and len(e) > 1,
                   'unsupported field term')
        return self.field_of(e[1])

    def flatten(self, e):
        if isinstance(e, list) and e and e[0] == 'and':
            for child in e[1:]:
                yield from self.flatten(child)
            return
        original = e
        if isinstance(e, list) and len(e) == 2 and e[0] == 'not':
            eq = e[1]
            fc.require(isinstance(eq, list) and len(eq) == 3 and eq[0] == '=',
                       'only conjunctions of field equalities/disequalities supported')
            p = self.field_of(eq[1])
            name = f'ff_witness_{len(self.witnesses)}'
            while name in self.reserved:
                name += '_'
            self.reserved.add(name)
            self.declarations[name] = (name, p)
            difference = ['ff.add', eq[1], ['ff.neg', eq[2]]]
            # The choice binder must also be fresh: otherwise it could capture
            # an original variable inside the difference term.
            binder = name + '_bound'
            while binder in self.reserved:
                binder += '_'
            self.reserved.add(binder)
            choice = ['choice', [[binder, ['_', 'FiniteField', str(p)]]],
                      ['=', ['ff.mul', binder, difference], numeral(1, p)]]
            self.witnesses[name] = choice
            e = ['=', ['ff.add', ['ff.mul', difference, name], numeral(-1, p)], numeral(0, p)]
        fc.require(isinstance(e, list) and len(e) == 3 and e[0] == '=',
                   'only conjunctions of field equalities/disequalities supported')
        self.literals.append(original)
        yield e

    def term_text(self, e, choices=False):
        """Use the external checker's numeral spelling; remove checked ascriptions."""
        if isinstance(e, str):
            if choices and e in self.witnesses:
                return self.term_text(self.witnesses[e], choices=False)
            if e.startswith('#f'):
                return e
            return e
        if e[0] == 'as':
            p = self.sort(e[2])
            if isinstance(e[1], str) and e[1].startswith('ff') and e[1][2:].lstrip('-').isdigit():
                return ['as', e[1], ['_', 'FiniteField', str(p)]]
            return self.term_text(e[1], choices)
        # ff.bitsum is not implemented by this Carcara revision. Reject instead
        # of silently treating it as an opaque polynomial variable.
        fc.require(e[0] != 'ff.bitsum', 'Carcara profile does not support ff.bitsum')
        return [self.term_text(x, choices) for x in e]

    def normalized(self):
        lines = ['(set-logic QF_FF)']
        for name, p in self.declarations.values():
            lines.append(fc.sexpr(['declare-const', name, ['_', 'FiniteField', str(p)]]))
        lines += [fc.sexpr(['assert', self.term_text(eq)]) for eq in self.equations]
        return '\n'.join(lines) + '\n'


def pac_polynomial(value):
    """Fixed variable numbering shared with the checked DAG; no user PAC names."""
    terms = []
    for mon, c in sorted(value.items(), reverse=True):
        factors = [str(c)]
        for v, exponent in sorted(Counter(mon).items()):
            factors.append(f'v{v + 1}' + (f'^{exponent}' if exponent > 1 else ''))
        terms.append('*'.join(factors))
    return ' + '.join(terms) or '0'


def export_pac(cert, values):
    """Translate only the root's ancestors; retain sharing instead of flattening.

    Each PAC linear combination has the same polynomial value as its DAG node.
    FFPacheck additionally reduces x^p=x, which preserves every such identity.
    """
    nodes, root = cert[':nodes'], fc.natural(cert[':root'])
    used, pending = set(), [root]
    while pending:
        i = pending.pop()
        if i in used:
            continue
        used.add(i)
        n = nodes[i]
        if n[0] == 'add':
            pending.extend([int(n[1]), int(n[2])])
        elif n[0] == 'mul':
            pending.append(int(n[1]))
    p = int(cert[':modulus'])
    ar = fc.Arithmetic(p)
    inputs = [fc.decode_polynomial(f, ar, len(cert[':variables'])) for f in cert[':inputs']]
    lines = [f'm {p};']
    # All input axioms appear in their original order, even if unused. The
    # independent bundle check binds this exact list to the original formula.
    lines += [f'a {i + 1} {pac_polynomial(f)};' for i, f in enumerate(inputs)]
    ids, fresh = {}, len(inputs) + 1
    for i in sorted(used):
        n = nodes[i]
        if n[0] == 'input':
            ids[i] = int(n[1]) + 1
            continue
        if n[0] == 'add':
            op = f'{ids[int(n[1])]}*(1) + {ids[int(n[2])]}*(1)'
        else:
            factor = {tuple(map(int, n[3])): int(n[2])}
            op = f'{ids[int(n[1])]}*({pac_polynomial(factor)})'
        lines.append(f'l {fresh} {op}, {pac_polynomial(values[i])};')
        ids[i] = fresh
        fresh += 1
    # An axiom 1 alone does not close FFPacheck's branch; a checked inference does.
    if nodes[root][0] == 'input':
        lines.append(f'l {fresh} {ids[root]}*(1), 1;')
    lines.append('unsat')
    return '\n'.join(lines) + '\n'


def export_artifact(original, dag):
    bridge = LiteralProblem(original)
    normalized = bridge.normalized()
    _, cert, values = fc.verify(normalized, dag)
    p = int(cert[':modulus'])
    variables = [bridge.term_text(v, choices=True) for v in cert[':variables']]
    pac = export_pac(cert, values)
    lines = ['; Z3 FF artifact profile: checked original-input bridge + Alethe/PAC.']
    serial = 0

    def step(clause, rule, premises=(), args=None):
        nonlocal serial
        name = f't{serial}'; serial += 1
        s = ['step', name, ['cl'] + clause, ':rule', rule]
        if premises:
            s += [':premises', list(premises)]
        if args is not None:
            s += [':args', args]
        lines.append(fc.sexpr(s))
        return name

    leaves = []
    def project(term, proof):
        if isinstance(term, list) and term[0] == 'and':
            for j, child in enumerate(term[1:]):
                child_proof = step([child], 'and', [proof], [str(j)])
                project(child, child_proof)
        else:
            leaves.append(proof)

    for i, assertion in enumerate(bridge.assertions):
        name = f'a{i}'
        lines.append(fc.sexpr(['assume', name, assertion]))
        project(bridge.term_text(bridge.expand(assertion)), name)
    fc.require(len(leaves) == len(bridge.equations), 'literal projection mismatch')

    def transfer(source, target, equivalence, premise):
        implication = step([['not', source], target], 'equiv1', [equivalence])
        return step([target], 'resolution', [implication, premise])

    converted, polynomials = [], []
    for i, (literal, equation, premise) in enumerate(zip(bridge.literals, bridge.equations, leaves)):
        literal = bridge.term_text(literal)
        equation = bridge.term_text(equation, choices=True)
        if literal[0] == 'not':
            witness = bridge.term_text(bridge.equations[i][1][1][2], choices=True)
            equivalence = step([['=', literal, equation]], 'ff_diseq',
                               args=[literal[1][1], literal[1][2], witness])
            premise = transfer(literal, equation, equivalence, premise)
        ar = fc.Arithmetic(p)
        value = fc.decode_polynomial(cert[':inputs'][i], ar, len(variables))
        poly = bridge.term_text(fc.polynomial_term(value, p, variables))
        polynomials.append(poly)
        canonical = ['=', poly, numeral(0, p)]
        left = ['ff.mul', numeral(1, p), ['ff.add', equation[1], ['ff.neg', equation[2]]]]
        right = ['ff.mul', numeral(1, p), ['ff.add', poly, ['ff.neg', numeral(0, p)]]]
        # Polynomial normalization checks 1*(lhs-rhs) = 1*(poly-0).
        # Since the scale is the unit 1, poly_simp_rel proves equivalence of
        # the equalities; resolution transfers the already justified premise.
        identity = step([['=', left, right]], 'poly_simp')
        equivalence = step([['=', equation, canonical]], 'poly_simp_rel', [identity])
        converted.append(transfer(equation, canonical, equivalence, premise))
    eqs = [['=', poly, numeral(0, p)] for poly in polynomials]
    conjunction = converted[0] if len(eqs) == 1 else step([['and'] + eqs], 'and_intro', converted)
    nonempty = ['not', ['set.is_empty', ['@ff.variety', ['@ff.ideal'] + polynomials]]]
    conversion = step([nonempty], 'ff_poly_conversion', [conjunction])
    lines.append(f'(step contradiction (cl) :rule ff_pac :premises ({conversion}) :args ({pac}))')
    alethe = '\n'.join(lines) + '\n'
    fc.require(len(alethe.encode()) <= LIMIT and len(pac.encode()) <= LIMIT, 'export size limit')
    return normalized, alethe, pac


def read(path):
    with Path(path).open('rb') as f:
        data = f.read(LIMIT + 1)
    fc.require(len(data) <= LIMIT, 'file size limit')
    return data.decode('utf-8')


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def run(argv, timeout, input_text=None):
    """Bounded output and wall time, killing the entire external process group."""
    start = time.monotonic()
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err, tempfile.TemporaryFile() as inp:
        if input_text is not None:
            inp.write(input_text.encode()); inp.seek(0)
        child = subprocess.Popen(argv, stdin=inp, stdout=out, stderr=err, start_new_session=True)
        try:
            while child.poll() is None:
                fc.require(time.monotonic() - start < timeout, 'external stage timeout')
                fc.require(os.fstat(out.fileno()).st_size <= LIMIT and os.fstat(err.fileno()).st_size <= LIMIT,
                           'external output limit')
                # Wait for early completion instead of imposing 20ms on every
                # tiny field lemma. Keep output/deadline supervision bounded.
                try:
                    child.wait(timeout=0.02)
                except subprocess.TimeoutExpired:
                    pass
        finally:
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
        out.seek(0); err.seek(0)
        stdout, stderr = out.read(LIMIT + 1), err.read(LIMIT + 1)
        fc.require(len(stdout) <= LIMIT and len(stderr) <= LIMIT, 'external output limit')
    result = dict(argv=list(map(str, argv)), seconds=time.monotonic() - start,
                  returncode=child.returncode, stdout=stdout.decode(errors='replace'), stderr=stderr.decode(errors='replace'))
    fc.require(child.returncode == 0, f'external stage failed: {result}')
    return result


def prepare_profile(original):
    """Keep the cheaper v1 path when applicable; use v2 for Boolean/deep input."""
    try:
        return 'literal', LiteralProblem(original).normalized()
    except (fc.Invalid, RecursionError):
        import ff_boolean_proof as bp
        bp.Graph(original)  # Validate supported sorts/commands before writing.
        return 'boolean', None


def produce_bundle(original, directory, z3, timeout=10, prepared=None):
    profile, normalized = prepare_profile(original) if prepared is None else prepared
    directory = Path(directory)
    if profile == 'boolean':
        import ff_boolean_proof as bp
        count = bp.produce_bundle(original, directory, z3, timeout)
        return dict(profile='z3-ff-alethe-pac-v2', field_lemmas=count)
    cmd = normalized + f'(ff-certify :timeout {max(1, int(timeout * 900))})\n'
    result = run([str(z3), '-in'], timeout, cmd)
    dag = result['stdout']
    fc.require(dag.lstrip().startswith('(ff-certificate\n'), 'no certificate: ' + dag[:1000])
    normalized, alethe, pac = export_artifact(original, dag)
    for name, data in [('certificate.ffcert', dag), ('polynomial-input.smt2', normalized),
                       ('proof.alethe', alethe), ('proof.pac', pac)]:
        (directory / name).write_text(data)
    return dict(profile='z3-ff-alethe-pac-v1', z3=result, field_lemmas=1)


def check_bundle(directory, carcara, ffpacheck, timeout=10):
    directory = Path(directory)
    if (directory / 'boolean-certificate.json').exists():
        fc.require(not (directory / 'certificate.ffcert').exists(), 'ambiguous proof bundle profile')
        import ff_boolean_proof as bp
        return bp.check_bundle(directory, carcara, ffpacheck, timeout)
    original, dag = read(directory / 'problem.smt2'), read(directory / 'certificate.ffcert')
    normalized, alethe, pac = export_artifact(original, dag)
    # Exact bytes are deliberately required by this versioned export profile.
    # This rejects changed axioms, variable maps, modulus, Alethe premises,
    # assertions, conclusions, admitted rules and trailing proof material.
    for name, expected in [('polynomial-input.smt2', normalized), ('proof.alethe', alethe), ('proof.pac', pac)]:
        fc.require(read(directory / name) == expected, f'input/proof binding mismatch: {name}')
    results = {}
    results['ffpacheck'] = run([str(ffpacheck), str(directory / 'proof.pac')], timeout)
    results['carcara'] = run([str(carcara), 'check', str(directory / 'proof.alethe'),
                              str(directory / 'problem.smt2'), '--expand-let-bindings',
                              '--apply-function-defs', '--ff-pac-solver', str(ffpacheck)], timeout)
    fc.require(results['carcara']['stdout'].strip() == 'valid', 'Carcara did not report a fully valid proof')
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('problem', type=Path, nargs='?')
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--z3', type=Path)
    parser.add_argument('--carcara', type=Path, required=True)
    parser.add_argument('--ffpacheck', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=10, help='seconds per external stage')
    parser.add_argument('--check', action='store_true', help='recheck an existing bundle; never regenerate proof bytes')
    args = parser.parse_args()
    start = time.monotonic()
    try:
        fc.require(0 < args.timeout <= 3600, 'invalid timeout')
        results = {}
        if not args.check:
            fc.require(args.problem and args.z3, 'production requires problem and --z3')
            original = read(args.problem)
            prepared = prepare_profile(original)
            args.out.mkdir(parents=True, exist_ok=False)
            (args.out / 'problem.smt2').write_text(original)
            results.update(produce_bundle(original, args.out, args.z3.resolve(), args.timeout, prepared))
        results.update(check_bundle(args.out.resolve(), args.carcara.resolve(), args.ffpacheck.resolve(), args.timeout))
        results['status'] = 'checked'
        results['profile'] = 'z3-ff-alethe-pac-v2' if (args.out / 'boolean-certificate.json').exists() else 'z3-ff-alethe-pac-v1'
        results['tested_checker_sources'] = dict(carcara=CARCARA_REVISION, ffpacheck=FFPACHECK_REVISION,
            patch='https://github.com/Z3Prover/z3test/blob/cb0b0d1e036ad30d27112ab7bfc02bf48fc9c0fb/regressions/finite_field/proof_checkers/ffpacheck-completion.patch')
        results['total_seconds'] = time.monotonic() - start
        results['files'] = {p.name: dict(sha256=digest(p), bytes=p.stat().st_size)
                            for p in args.out.iterdir() if p.suffix in ('.smt2', '.ffcert', '.alethe', '.pac') or p.name == 'boolean-certificate.json'}
        results['binaries'] = {name: dict(path=str(path.resolve()), sha256=digest(path))
                               for name, path in [('z3', args.z3), ('carcara', args.carcara), ('ffpacheck', args.ffpacheck)] if path}
        (args.out / ('recheck.json' if args.check else 'result.json')).write_text(json.dumps(results, indent=2) + '\n')
        print(f'checked original-input Alethe/PAC refutation: {args.out} ({results["total_seconds"]:.3f}s)')
        return 0
    except (fc.Invalid, OSError, ValueError, TypeError, IndexError, KeyError, RecursionError) as error:
        print(f'proof pipeline rejected: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
