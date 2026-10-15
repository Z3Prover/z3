#!/usr/bin/env python3
"""Replay and export FF leaves from native Z3 proofs, without reconstruction.

Z3 supplies AST access only. Polynomial arithmetic and premise/definition binding
are checked here independently. An exported bundle certifies a FIELD LEMMA;
composition with assertions and other theories remains in the native proof.
The encoded equations alone are not a proof of the original SMT input.
"""
from pathlib import Path
import re
import z3
import ff_certificate as fc
import ff_proof_pipeline as pp

require = fc.require
OPS = {z3.Z3_OP_FF_ADD, z3.Z3_OP_FF_MUL, z3.Z3_OP_FF_NEG, z3.Z3_OP_FF_BITSUM}


def signed(lit):
    negative = False
    while z3.is_not(lit):
        negative = not negative
        lit = lit.arg(0)
    return lit.get_id(), negative


def _encode(evidence):
    """Bind the native definition/input indices and replay through the v1 DAG checker."""
    require(z3.is_app(evidence) and str(evidence.decl().name()) == 'ff-pac'
            and evidence.num_args() == 2, 'malformed native FF evidence')
    ps, root = evidence.children()
    require(z3.is_app(ps) and str(ps.decl().name()) == 'ff-premises'
            and 0 < ps.num_args() <= 4096, 'malformed native premises')
    first = ps.arg(0)
    if z3.is_not(first): first = first.arg(0)
    require(z3.is_eq(first) and isinstance(first.arg(0).sort(), z3.FiniteFieldSortRef), 'not a field premise')
    field = first.arg(0).sort()
    p = field.size()
    ar = fc.Arithmetic(p)
    terms, equations, variables = {}, [], []
    bindings, origins = [], []

    def fresh(binding):
        require(len(variables) < 4096, 'native variable limit')
        v = len(variables)
        variables.append('v' + str(v))
        bindings.append(binding)
        return {(v,): 1}

    def term(t):
        pending = [t]
        while pending:
            ar.tick()
            a = pending[-1]; key = a.get_id()
            if key in terms:
                pending.pop(); continue
            require(z3.is_app(a) and a.sort().eq(field), 'native field term sort')
            op = a.decl().kind()
            if op in OPS:
                # Native indices use a stack: enqueue operands in source order,
                # then visit the last pending operand first. Left and right
                # equality operands are completed separately, in that order.
                missing = [x for x in a.children() if x.get_id() not in terms]
                if missing:
                    pending.extend(missing); continue
                args = [terms[x.get_id()] for x in a.children()]
                require(len(args) == 1 if op == z3.Z3_OP_FF_NEG else len(args) >= 1, 'native operator arity')
                value = {(): 1} if op == z3.Z3_OP_FF_MUL else {}
                for i, arg in enumerate(args):
                    if op == z3.Z3_OP_FF_MUL: value = ar.mul(value, arg)
                    else: value = ar.add(value, arg, -1 if op == z3.Z3_OP_FF_NEG else pow(2, i, p) if op == z3.Z3_OP_FF_BITSUM else 1)
                v = fresh(a)
                equations.append(ar.add(v, value, -1))
                origins.append(None)
                value = v
            elif op == z3.Z3_OP_FF_NUM:
                c = a.as_long(); require(0 <= c < p, 'native coefficient range')
                value = {(): c} if c else {}
            else:
                # A foreign field-valued application is opaque; its arguments
                # and congruence are premises of the surrounding native proof.
                value = fresh(a)
            terms[key] = value
            pending.pop()
        return terms[t.get_id()]

    for premise_index, literal in enumerate(ps.children()):
        positive = not z3.is_not(literal)
        eq = literal if positive else literal.arg(0)
        require(z3.is_eq(eq) and eq.arg(0).sort().eq(field) and eq.arg(1).sort().eq(field), 'native premise sort')
        left, right = term(eq.arg(0)), term(eq.arg(1))
        value = ar.add(left, right, -1)
        if not positive:
            value = ar.add(ar.mul(fresh(('inverse', eq)), value), {(): p - 1})
        equations.append(value)
        origins.append(premise_index)
    if p <= 31:
        # Every F_p value, including definitional and inverse variables,
        # satisfies Fermat. These are not arbitrary extra assumptions.
        for v in range(len(variables)):
            equations.append(ar.add({(v,) * p: 1}, {(v,): 1}, -1))
            origins.append("fermat")
    require(len(equations) <= 4096, 'external profile equation limit')
    nodes, ids, pending = [], {}, [root]
    while pending:
        ar.tick()
        a = pending[-1]; key = a.get_id()
        if key in ids:
            pending.pop(); continue
        require(z3.is_app(a) and a.sort().eq(root.sort()), 'native proof node sort')
        rule = str(a.decl().name()); args = a.children()
        require((rule == 'ff-input' and len(args) == 1) or
                (rule == 'ff-add' and len(args) == 2) or
                (rule == 'ff-mul' and len(args) >= 2), 'native proof rule/arity')
        children = [] if rule == 'ff-input' else args if rule == 'ff-add' else args[:1]
        missing = [x for x in children if x.get_id() not in ids]
        if missing:
            pending.extend(missing); continue
        if rule == 'ff-input':
            require(z3.is_int_value(args[0]), 'native input index')
            node = ['input', str(args[0].as_long())]
        elif rule == 'ff-add':
            node = ['add', str(ids[args[0].get_id()]), str(ids[args[1].get_id()])]
        else:
            require(args[1].sort().eq(field) and args[1].decl().kind() == z3.Z3_OP_FF_NUM, 'native multiplier coefficient')
            require(all(z3.is_int_value(x) for x in args[2:]), 'native multiplier indices')
            mon = [x.as_long() for x in args[2:]]
            require(mon == sorted(mon) and all(0 <= v < len(variables) for v in mon), 'native multiplier variables')
            left = ids[args[0].get_id()]; c = args[1].as_long()
            if c == 0:
                # The external profile uses nonzero coefficients. Record the
                # same zero as f + (-f), without adding a synthetic input.
                nodes.append(['mul', str(left), str(p - 1), []])
                node = ['add', str(left), str(len(nodes) - 1)]
            else:
                node = ['mul', str(left), str(c), list(map(str, mon))]
        require(len(nodes) < 100000, 'native proof node limit')
        ids[key] = len(nodes); nodes.append(node); pending.pop()
    zero = ['as', 'ff0', ['_', 'FiniteField', str(p)]]
    problem = '(set-logic QF_FF)\n' + ''.join(f'(declare-const {v} (_ FiniteField {p}))\n' for v in variables)
    problem += ''.join(fc.sexpr(['assert', ['=', fc.polynomial_term(f, p, variables), zero]]) + '\n' for f in equations)
    raw = lambda f: [[str(c)] + list(map(str, mon)) for mon, c in sorted(f.items())]
    dag = fc.sexpr(['ff-certificate', ':version', '1', ':modulus', str(p), ':variables', variables,
                   ':inputs', [raw(f) for f in equations], ':nodes', nodes, ':root', str(ids[root.get_id()])]) + '\n'
    _, cert, values = fc.verify(problem, dag)
    return problem, dag, bindings, origins, cert, values


def encode(evidence, with_bindings=False):
    result = _encode(evidence)
    return result[:4] if with_bindings else result[:2]


def replay_lemma(lemma):
    """Validate the clause and return its independently replayed evidence once.

    Exporters need the bindings and intermediate polynomials as well as the
    serialized DAG. Returning them from the same checked replay avoids repeating
    expensive arithmetic; there is no path that skips premise or DAG checking.
    """
    require(z3.is_app(lemma) and lemma.decl().kind() == z3.Z3_OP_PR_TH_LEMMA and lemma.num_args() == 1, 'native leaf expected')
    params = lemma.decl().params()
    require(len(params) == 3 and params[:2] == ['ff', 'pac'], 'native FF rule expected')
    evidence = params[2]
    result = _encode(evidence)
    todo, literals, true = [lemma.arg(0)], set(), False
    while todo:
        f = todo.pop()
        if z3.is_or(f): todo.extend(f.children())
        elif z3.is_true(f): true = True
        else: literals.add(signed(f))
    for p in evidence.arg(0).children():
        atom, neg = signed(p)
        require(true or (atom, not neg) in literals, 'native lemma removed a certified literal')
    return result


def check_lemma(lemma):
    return replay_lemma(lemma)[:2]


def artifacts(lemma):
    problem, dag = check_lemma(lemma)
    normalized, alethe, pac = pp.export_artifact(problem, dag)
    return {'encoded-input.smt2': problem, 'certificate.ffcert': dag,
            'polynomial-input.smt2': normalized, 'proof.alethe': alethe, 'proof.pac': pac}


def check_bundle(lemma, directory, carcara, ffpacheck, timeout=10):
    """The caller must supply the native leaf again: detached equations are insufficient."""
    directory = Path(directory)
    for name, expected in artifacts(lemma).items():
        require((directory / name).read_text() == expected, 'native leaf binding mismatch: ' + name)
    pac = pp.run([str(ffpacheck), str(directory / 'proof.pac')], timeout)
    alethe = pp.run([str(carcara), 'check', str(directory / 'proof.alethe'),
                    str(directory / 'encoded-input.smt2'), '--expand-let-bindings',
                    '--apply-function-defs', '--ff-pac-solver', str(ffpacheck)], timeout)
    pac_lines = re.sub(r'\x1b\[[0-9;]*m', '', pac['stdout']).splitlines()
    require(any(line.strip() == 'PROOF CHECK: SUCCEEDED' for line in pac_lines), 'PAC completion marker missing')
    require(alethe['stdout'].strip() == 'valid', 'Alethe completion marker missing')
    return pac, alethe
