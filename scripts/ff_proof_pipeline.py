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


def pac_polynomial(value, modulus=None):
    """Fixed variable numbering shared with the checked DAG; no user PAC names."""
    terms = []
    for mon, c in sorted(value.items(), reverse=True):
        # PAC coefficients are integers interpreted modulo the declared prime.
        # Centering avoids spelling -1 as a hundreds-of-bits positive integer.
        # The independent DAG replay still uses canonical residues throughout.
        if modulus is not None and c > modulus // 2:
            c -= modulus
        factors = [str(c)]
        for v, exponent in sorted(Counter(mon).items()):
            factors.append(f'v{v + 1}' + (f'^{exponent}' if exponent > 1 else ''))
        terms.append('*'.join(factors))
    return ' + '.join(terms) or '0'


class PacWriter:
    """Bounded PAC output from individually checked DAG values.

    Only root ancestors are exported, with sharing intact. All input axioms
    retain their original order for independent original-formula binding.
    """
    def __init__(self, cert):
        self.nodes, self.root = cert[':nodes'], fc.natural(cert[':root'])
        self.used, pending = set(), [self.root]
        while pending:
            i = pending.pop()
            if i in self.used:
                continue
            self.used.add(i)
            n = self.nodes[i]
            if n[0] == 'add':
                pending.extend([int(n[1]), int(n[2])])
            elif n[0] == 'mul':
                pending.append(int(n[1]))
        p = int(cert[':modulus'])
        self.modulus = p
        ar = fc.Arithmetic(p)
        self.lines, self.size = [], 0
        self.emit(f'm {p};')
        for i, raw in enumerate(cert[':inputs']):
            value = fc.decode_polynomial(raw, ar, len(cert[':variables']))
            self.emit(f'a {i + 1} {pac_polynomial(value, self.modulus)};')
        self.ids, self.fresh = {}, len(cert[':inputs']) + 1

    def emit(self, line):
        self.size += len(line.encode('utf-8')) + 1
        fc.require(self.size <= 32 * 1024 * 1024, 'PAC output byte limit')
        self.lines.append(line)

    def node(self, i, value):
        if i not in self.used:
            return
        n = self.nodes[i]
        if n[0] == 'input':
            self.ids[i] = int(n[1]) + 1
            return
        if n[0] == 'add':
            op = f'{self.ids[int(n[1])]}*(1) + {self.ids[int(n[2])]}*(1)'
        else:
            factor = {tuple(map(int, n[3])): int(n[2])}
            op = f'{self.ids[int(n[1])]}*({pac_polynomial(factor, self.modulus)})'
        self.emit(f'l {self.fresh} {op}, {pac_polynomial(value, self.modulus)};')
        self.ids[i] = self.fresh
        self.fresh += 1

    def finish(self):
        # An axiom 1 alone does not close FFPacheck; a checked inference does.
        if self.nodes[self.root][0] == 'input':
            self.emit(f'l {self.fresh} {self.ids[self.root]}*(1), 1;')
        self.emit('unsat')
        return '\n'.join(self.lines) + '\n'


class CompactPacWriter(PacWriter):
    """Inline bounded low-fan-out steps into PAC linear combinations.

    Frequently shared nodes stay as named anchors. Every original DAG node is still
    independently replayed; this only avoids printing its expanded polynomial
    when no later PAC step needs to refer to it separately.
    """
    def __init__(self, cert):
        super().__init__(cert)
        self.ar = fc.Arithmetic(int(cert[':modulus']))
        self.work = 0
        uses = [0] * len(self.nodes)
        for i in self.used:
            n = self.nodes[i]
            parents = n[1:3] if n[0] == 'add' else n[1:2] if n[0] == 'mul' else []
            for parent in parents:
                uses[int(parent)] += 1
        # Naming every twice-used node can print a large polynomial merely to
        # save two short multiplier expressions. Inline low fan-out nodes, but
        # cap each expanded combination at 1024 DAG leaves to avoid exponential
        # duplication. Higher fan-out nodes retain explicit sharing.
        self.anchors, expansion = set(), {}
        for i in sorted(self.used):
            n = self.nodes[i]
            parents = n[1:3] if n[0] == 'add' else n[1:2] if n[0] == 'mul' else []
            cost = sum(expansion[int(j)] for j in parents) or 1
            if n[0] == 'input' or i == self.root or uses[i] > 2 or cost > 1024:
                self.anchors.add(i)
                expansion[i] = 1
            else:
                expansion[i] = cost

    def node(self, i, value):
        if i not in self.anchors:
            return
        if self.nodes[i][0] == 'input':
            return super().node(i, value)
        terms, pending = {}, [(i, 1, ())]
        while pending:
            j, coefficient, mon = pending.pop()
            self.work += 1 + len(mon)
            fc.require(self.work <= 2000000, 'PAC composition work limit')
            if j != i and j in self.anchors:
                key = j, mon
                terms[key] = (terms.get(key, 0) + coefficient) % self.ar.p
                continue
            n = self.nodes[j]
            if n[0] == 'add':
                pending.extend((int(parent), coefficient, mon) for parent in n[1:3])
            else:
                factor = tuple(map(int, n[3]))
                fc.require(len(mon) + len(factor) <= 1024, 'PAC composition degree limit')
                pending.append((int(n[1]), coefficient * int(n[2]) % self.ar.p, tuple(sorted(mon + factor))))
        grouped = {}
        for (j, mon), c in sorted(terms.items()):
            if c:
                grouped.setdefault(j, {})[mon] = c
        # Cancellation can produce a zero node; express it as 0 times a proved
        # input rather than introduce a new axiom. PAC checks this inference.
        if not grouped:
            grouped[next(j for j in self.ids if self.nodes[j][0] == 'input')] = {}
        op = ' + '.join(f'{self.ids[j]}*({pac_polynomial(f, self.modulus)})' for j, f in grouped.items())
        self.emit(f'l {self.fresh} {op}, {pac_polynomial(value, self.modulus)};')
        self.ids[i] = self.fresh
        self.fresh += 1


def export_pac(cert, values):
    writer = PacWriter(cert)
    for i in range(len(cert[':nodes'])):
        writer.node(i, values[i])
    return writer.finish()


def verified_pac(problem, dag, *, compact=True):
    writer = None
    def emit(cert, i, value):
        nonlocal writer
        if writer is None:
            writer = CompactPacWriter(cert) if compact else PacWriter(cert)
        writer.node(i, value)
    _, cert, _ = fc.verify_problem(problem, dag, retain_values=False, on_node=emit)
    # Never publish provisional PAC output before the entire replay succeeds.
    return cert, writer.finish()


def export_artifact(original, dag):
    bridge = LiteralProblem(original)
    normalized = bridge.normalized()
    cert, pac = verified_pac(fc.Problem(normalized), dag)
    p = int(cert[':modulus'])
    variables = [bridge.term_text(v, choices=True) for v in cert[':variables']]
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
        # Popen.wait(timeout) uses an exponential sleep loop on POSIX. A
        # blocking waiter notifies completion immediately while this thread
        # retains the same bounded output and wall-time supervision.
        import threading
        completed = threading.Event()
        wait_errors = []
        def wait_for_exit():
            try: child.wait()
            except Exception as error: wait_errors.append(error)
            finally: completed.set()
        waiter = threading.Thread(target=wait_for_exit, daemon=True)
        try:
            waiter.start()
            while not completed.is_set():
                remaining = timeout - (time.monotonic() - start)
                fc.require(remaining > 0, 'external stage timeout')
                fc.require(os.fstat(out.fileno()).st_size <= LIMIT and os.fstat(err.fileno()).st_size <= LIMIT,
                           'external output limit')
                completed.wait(min(.02, remaining))
        finally:
            if not completed.is_set():
                try: os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError: pass
            if waiter.ident is not None: waiter.join()
            else: child.wait()
        if wait_errors: raise wait_errors[0]
        out.seek(0); err.seek(0)
        stdout, stderr = out.read(LIMIT + 1), err.read(LIMIT + 1)
        fc.require(len(stdout) <= LIMIT and len(stderr) <= LIMIT, 'external output limit')
    result = dict(argv=list(map(str, argv)), seconds=time.monotonic() - start,
                  returncode=child.returncode, stdout=stdout.decode(errors='replace'), stderr=stderr.decode(errors='replace'))
    fc.require(child.returncode == 0, f'external stage failed: {result}')
    return result


class NativeSession:
    """One bounded, explicitly closed SMT command process (POSIX pipes).

    Drain stdout/stderr while writing so large clauses cannot deadlock the
    protocol. Every request shares the caller's absolute deadline. Solver output
    is untrusted and is validated by the existing model/RUP replay layer.
    """
    def __init__(self, binary):
        self.child = subprocess.Popen([str(binary), '-in'], stdin=subprocess.PIPE,
                                      stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                      start_new_session=True, bufsize=0)
        self.output = bytearray()
        self.errors = bytearray()
        self.closed = False
        try:
            for stream in [self.child.stdin, self.child.stdout, self.child.stderr]:
                os.set_blocking(stream.fileno(), False)
        except Exception:
            self.close()
            raise

    def exchange(self, text, deadline, delimiter=b'\n'):
        import selectors
        data = text.encode()
        offset = 0
        try:
            fc.require(len(data) <= LIMIT, 'native session input limit')
            fc.require(not self.closed, 'native session is closed')
            fc.require(isinstance(delimiter, bytes) and delimiter, 'invalid native session delimiter')
            with selectors.DefaultSelector() as ready:
                ready.register(self.child.stdin, selectors.EVENT_WRITE, 'input')
                ready.register(self.child.stdout, selectors.EVENT_READ, 'output')
                ready.register(self.child.stderr, selectors.EVENT_READ, 'errors')
                while True:
                    remaining = deadline - time.monotonic()
                    fc.require(remaining > 0, 'native session timeout')
                    if offset == len(data) and delimiter in self.output:
                        line, _, rest = self.output.partition(delimiter)
                        self.output = bytearray(rest)
                        fc.require(not self.errors, 'native session stderr: ' + self.errors.decode(errors='replace')[:1000])
                        return line.decode() + '\n'
                    for key, _ in ready.select(min(.05, remaining)):
                        if key.data == 'input':
                            try: offset += os.write(key.fd, data[offset:offset+65536])
                            except BlockingIOError: continue
                            if offset == len(data): ready.unregister(key.fileobj)
                        else:
                            try: chunk = os.read(key.fd, 65536)
                            except BlockingIOError: continue
                            fc.require(chunk, 'native session closed before response')
                            target = self.output if key.data == 'output' else self.errors
                            target.extend(chunk)
                            fc.require(len(target) <= LIMIT, 'native session output limit')
        except Exception:
            self.close()
            raise

    def close(self):
        if self.closed: return
        self.closed = True
        if self.child.poll() is None:
            try: os.killpg(self.child.pid, signal.SIGKILL)
            except ProcessLookupError: pass
            except PermissionError:
                if self.child.poll() is None: self.child.kill()
        self.child.wait()
        for stream in [self.child.stdin, self.child.stdout, self.child.stderr]: stream.close()

    def __del__(self):
        try: self.close()
        except Exception: pass


class FieldSession:
    """Reuse a process/AST manager, but isolate every field query's premises.

    Only generated Case.normalized() inputs are sent here. A fresh command scope
    owns assertions. Identical declarations may survive between requests, but
    no algebraic result or proof ID is reused. A changed declaration resets the
    command context before the next query.
    The nonce delimits multiline output, never authorizes a proof step.
    """
    def __init__(self, binary):
        self.session = NativeSession(binary)
        self.started = False
        self.declarations = {}
        self.declaration_bytes = 0

    def query(self, normalized, deadline, backend):
        import secrets
        header = '(set-logic QF_FF)\n'
        fc.require(normalized.startswith(header), 'expected normalized field query')
        remaining = deadline - time.monotonic()
        fc.require(remaining > 0, 'field session timeout')
        marker = 'ff_session_end_' + secrets.token_hex(16)
        import re
        fc.require(len(normalized.encode()) <= LIMIT, 'field session input limit')
        declarations, assertions = {}, []
        for line in normalized[len(header):].splitlines():
            if line.startswith('(assert '): assertions.append(line); continue
            match = re.match(r'^\((?:declare-const|define-fun) ([A-Za-z_][A-Za-z_0-9]*) ', line)
            fc.require(match is not None, 'unexpected normalized declaration')
            name = match[1]
            fc.require(name not in declarations, 'duplicate normalized declaration')
            declarations[name] = line
        new = {k: v for k, v in declarations.items() if k not in self.declarations}
        size = sum(len(v.encode())+1 for v in new.values())
        reset = any(k in self.declarations and self.declarations[k] != v for k,v in declarations.items())
        reset |= self.declaration_bytes + size > LIMIT
        if reset:
            new = declarations
            size = sum(len(v.encode())+1 for v in new.values())
        fc.require(size <= LIMIT, 'field declaration limit')
        text = '(reset)\n' if reset else ''
        if reset or not self.started: text += header
        text += ''.join(line+'\n' for line in new.values())
        text += '(push)\n' + ''.join(line+'\n' for line in assertions) + certificate_command(remaining, backend)
        text += f'(pop)\n(echo "{marker}")\n'
        result = self.session.exchange(text, deadline, ('\n' + marker + '\n').encode())
        if reset:
            self.declarations.clear(); self.declaration_bytes = 0
        self.declarations.update(new); self.declaration_bytes += size
        self.started = True
        return result

    def close(self):
        self.session.close()


def prepare_profile(original):
    """Keep the cheaper v1 path when applicable; use v2 for Boolean/deep input."""
    try:
        return 'literal', LiteralProblem(original).normalized()
    except (fc.Invalid, RecursionError):
        import ff_boolean_proof as bp
        bp.Graph(original)  # Validate supported sorts/commands before writing.
        return 'boolean', None


def certificate_command(timeout, backend="auto"):
    fc.require(backend in ("auto", "scalar", "f4", "native"), "invalid certificate backend")
    # Omitting auto preserves compatibility with pre-backend-selector binaries.
    option = "" if backend == "auto" else f" :backend {backend}"
    # Native recording charges both algebra and proof construction to this
    # allowance. The wall deadline and DAG/term/storage caps remain independent.
    if backend == 'native': option += ' :max_steps 20000000'
    return f"(ff-certify{option} :timeout {max(1, int(timeout * 900))})\n"


def produce_bundle(original, directory, z3, timeout=10, prepared=None, backend="auto", boolean_backend="auto", field_session=None):
    fc.require(backend in ("auto", "scalar", "f4", "native"), "invalid certificate backend")
    fc.require(boolean_backend in ("auto", "native", "incremental", "integrated", "ranges", "circuits", "legacy"), "invalid Boolean backend")
    profile, normalized = prepare_profile(original) if prepared is None else prepared
    directory = Path(directory)
    if profile == 'boolean':
        import ff_boolean_proof as bp
        count = bp.produce_bundle(original, directory, z3, timeout, backend, boolean_backend, field_session)
        return dict(profile='z3-ff-alethe-pac-v2', field_lemmas=count)
    cmd = normalized + certificate_command(timeout, backend)
    result = run([str(z3), '-in'], timeout, cmd)
    dag = result['stdout']
    fc.require(dag.lstrip().startswith('(ff-certificate\n'), 'no certificate: ' + dag[:1000])
    if backend == 'native': dag = fc.try_balance_certificate(dag)
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
    parser.add_argument('--backend', choices=['auto', 'scalar', 'f4', 'native'], default='auto', help='bounded polynomial certificate search')
    parser.add_argument('--boolean-backend', choices=['auto', 'native', 'incremental', 'integrated', 'ranges', 'circuits', 'legacy'], default='auto', help='Boolean certificate search; auto follows the polynomial backend')
    parser.add_argument('--field-session', action=argparse.BooleanOptionalAction, default=None,
                        help='reuse a scoped field-certificate process (default for native incremental search on POSIX)')
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
            results.update(produce_bundle(original, args.out, args.z3.resolve(), args.timeout, prepared, args.backend, args.boolean_backend, args.field_session))
        results.update(check_bundle(args.out.resolve(), args.carcara.resolve(), args.ffpacheck.resolve(), args.timeout))
        results['status'] = 'checked'
        if not args.check:
            results['certificate_backend'] = args.backend
            results['boolean_backend'] = args.boolean_backend
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
