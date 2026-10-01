"""Original-input Boolean/ITE proofs, deep DAGs, and independent corruptions."""
import argparse
import copy
import itertools
import json
from pathlib import Path
import random
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import ff_boolean_proof as bp
import ff_proof_pipeline as pp

LARGE = 21888242871839275222246405745257275088548364400416034343698204186575808495617


def source(body, p=7, extra=''):
    return f'(set-logic QF_FF)\n(define-sort F () (_ FiniteField {p}))\n(declare-const a Bool)\n(declare-const b Bool)\n(declare-const x F)\n(declare-const y F)\n{extra}\n{body}\n'


def reject(f):
    try: f()
    except (pp.fc.Invalid, OSError): return
    raise AssertionError('invalid certificate accepted')


def evaluate(g, assignment):
    """Tiny exhaustive semantic oracle, independent of the CNF/field encoders."""
    values = {}
    for i in range(1, g.source_nodes):
        op, args, data = g.nodes[i]; a = [values[x] for x in args]
        if op == 'var': v = assignment[data[0]]
        elif op == 'num': v = data[0] % data[1]
        elif op == 'true': v = True
        elif op == 'false': v = False
        elif op == 'and': v = all(a)
        elif op == 'or': v = any(a)
        elif op == 'not': v = not a[0]
        elif op == '=': v = a[0] == a[1]
        elif op == 'xor': v = a[0] != a[1]
        elif op == '=>': v = not a[0] or a[1]
        elif op == 'ite': v = a[1] if a[0] else a[2]
        elif op == 'ff.add': v = sum(a) % g.p
        elif op == 'ff.neg': v = -a[0] % g.p
        elif op == 'ff.mul':
            v = 1
            for x in a: v = v*x % g.p
        else: raise AssertionError(op)
        values[i] = v
    return all(values[a] for a in g.assertions)


def check_boolean_search():
    """Adjudicate SAT independently and replay every learned resolution clause."""
    rng = random.Random(926)
    clauses = [(1,), (-1,), (2,), (-2,), (1, 2), (1, -2), (-1, 2), (-1, -2)]
    cases = [[c for i, c in enumerate(clauses) if mask & (1 << i)] for mask in range(256)]
    for _ in range(128):
        cases.append([tuple(v if rng.randrange(2) else -v for v in rng.sample(range(1, 7), rng.randint(1, 4)))
                      for _ in range(rng.randint(5, 30))])
    checks, learned = 0, False
    for original in cases:
        original = [bp.clause(c) for c in original]
        search = bp.Search(original)
        # Reuse the search after adding a blocking clause, as field lemmas do.
        added = []
        for _ in range(3):
            assumptions = original + added
            variables = sorted({abs(x) for c in assumptions for x in c})
            expected = any(all(any(values[abs(x)] == (x > 0) for x in c) for c in assumptions)
                           for bits in itertools.product([False, True], repeat=len(variables))
                           for values in [dict(zip(variables, bits))])
            sat, result = search.search()
            assert sat == expected, (assumptions, sat, expected)
            replay = list(original)
            for record in search.records:
                if record['rule'] == 'field':
                    replay.append(tuple(record['clause']))
                else:
                    a, b, pivot = record['left'], record['right'], record['pivot']
                    assert 0 <= a < len(replay) and 0 <= b < len(replay)
                    assert pivot in replay[a] and -pivot in replay[b]
                    replay.append(bp.clause((set(replay[a]) - {pivot}) | (set(replay[b]) - {-pivot})))
            assert replay == search.clauses
            learned |= any(i >= len(original) and search.records[i-len(original)]['rule'] == 'resolve'
                           for i in search.active)
            checks += 1
            if not sat:
                assert replay[result] == ()
                break
            assert all(any(result.get(abs(x)) == (x > 0) for x in c) for c in assumptions)
            blocked = bp.clause(-v if result.get(v, False) else v for v in variables)
            added.append(blocked)
            search.append(blocked, dict(rule='field', clause=list(blocked)))
    assert learned
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['z3','carcara','ffpacheck']: parser.add_argument('--'+name, required=True)
    args = parser.parse_args()
    search_checks = check_boolean_search()
    checked, rejected, sat_count, unsat_count, unknown_count = 0, 0, 0, 0, 0
    with tempfile.TemporaryDirectory(prefix='ff-boolean-tests-') as temp:
        root = Path(temp)
        def certify(text):
            nonlocal checked
            proof = bp.produce(text, args.z3, 10)
            files = bp.verify_export(text, proof)
            d = root / str(checked); d.mkdir()
            (d/'problem.smt2').write_text(text)
            (d/'boolean-certificate.json').write_text(json.dumps(proof))
            for name, data in files.items(): (d/name).write_text(data)
            pp.check_bundle(d, args.carcara, args.ffpacheck, 10)
            checked += 1
            return proof, d
        laws = [
            '(or a (not a))',
            '(= (and a b) (not (or (not a) (not b))))',
            '(= (or a b) (not (and (not a) (not b))))',
            '(= (=> a b) (or (not a) b))',
            '(= (xor a b) (not (= a b)))',
            '(= (ite a b (not b)) (= a b))',
            '(= (not (not (not a))) (not a))',
            '(= (and a a) a)',
            '(= (or false a) a)',
            '(= (and true a) a)',
        ]
        for law in laws: certify(source(f'(assert (not {law}))'))
        for p in [2, 3, 7, LARGE]:
            for body in [
                '(assert (= x (ite a (as ff0 F) (as ff1 F))))\n(assert (and (not (= x (as ff0 F))) (not (= x (as ff1 F)))))',
                '(assert (not (= (ite a (ff.add x y) x) (ff.add x (ite a y (as ff0 F))))))',
                '(assert (= x y))\n(assert (not (= (ite (= x y) (as ff1 F) (as ff0 F)) (as ff1 F))))',
                '(assert (not (= (ite (xor a b) (ite a x y) y) (ite a (ite b y x) y))))',
            ]: certify(source(body,p))
        # Definitions/lets preserve lexical scope, including simultaneous binds.
        certify(source('(assert (and alias (not (let ((a b) (b a)) (= a b)))))',
                       extra='(define-fun alias () Bool (= a b))'))
        certify(source('(assert (let ((a (not a))) (and a (not a))))',
                       extra='(declare-const ff_proof_t1 F)\n(declare-const |quoted x| F)'))
        # An externally checked long let chain that exceeded the old parser.
        deep = '(not (= x x))'
        for i in range(800): deep = f'(let ((l{i} x)) {deep})'
        certify(source('(assert '+deep+')'))
        # Much deeper expansion is stack-safe; no external checker stack promise.
        deep = '(and a (not a))'
        for i in range(12000): deep = f'(let ((l{i} a)) {deep})'
        g = bp.Graph(source('(assert '+deep+')'))
        assert len(g.nodes) < 20
        negations = '(not ' * 12001 + 'true' + ')' * 12001
        g = bp.Graph(source('(assert ' + negations + ')'))
        assert g.lit(g.assertions[0]) < 0
        # Exponential tree expansion becomes a small shared DAG and proof text.
        chain = '(assert (not (= t400 t400)))'
        for i in reversed(range(1,401)):
            chain = f'(define-fun t{i} () Bool (and t{i-1} t{i-1}))\n' + chain
        text = source(chain,extra='(define-fun t0 () Bool a)')
        g=bp.Graph(text); assert len(g.nodes) < 410
        proof=bp.produce(text,args.z3,10); files=bp.verify_export(text,proof)
        assert len(files['proof.alethe']) < 1000000
        # Exhaustively adjudicate randomized mixed formulas over tiny fields.
        rng=random.Random(1919)
        for p in [2,3]:
            atoms=['a','b','(= x y)','(= x (as ff0 F))','(= (ff.mul x y) (as ff1 F))',
                   '(= x (ite a (as ff0 F) (as ff1 F)))']
            for _ in range(18):
                terms=list(atoms)
                for __ in range(5):
                    op=rng.choice(['and','or','xor','=>','='])
                    terms.append(f'({op} {rng.choice(terms)} {rng.choice(terms)})')
                body=f'(and {rng.choice(terms)} (not {rng.choice(terms)}))'
                text=source('(assert '+body+')',p); g=bp.Graph(text)
                sat=any(evaluate(g,dict(zip(['a','b','x','y'],v))) for v in itertools.product([False,True],[False,True],range(p),range(p)))
                try: proof=bp.produce(text,args.z3,3)
                except pp.fc.Invalid:
                    if sat: sat_count+=1
                    else: unknown_count+=1
                else:
                    assert not sat,'SAT formula certified UNSAT'
                    bp.verify_export(text,proof); unsat_count+=1
        text=source('(assert (= x (ite a (as ff0 F) (as ff1 F))))\n(assert (and (not (= x (as ff0 F))) (not (= x (as ff1 F)))))')
        proof,d=certify(text)
        def mutated(edit):
            nonlocal rejected
            bad=copy.deepcopy(proof); edit(bad); reject(lambda:bp.verify_export(text,bad)); rejected+=1
        mutated(lambda p:p.update(root=0))
        mutated(lambda p:p.update(records=[]))
        mutated(lambda p:p.update(version=99))
        mutated(lambda p:p.update(extra='unchecked'))
        ri=next(i for i,r in enumerate(proof['records']) if r['rule']=='resolve')
        fi=next(i for i,r in enumerate(proof['records']) if r['rule']=='field')
        mutated(lambda p:p['records'][ri].update(left=999999))
        mutated(lambda p:p['records'][ri].update(pivot=0))
        mutated(lambda p:p['records'][ri].update(pivot=-p['records'][ri]['pivot']))
        mutated(lambda p:p['records'][fi].update(literals=p['records'][fi]['literals'][:-1]))
        mutated(lambda p:p['records'][fi].update(certificate=p['records'][fi]['certificate'].replace(':modulus 7',':modulus 3')))
        mutated(lambda p:p['records'][fi].update(literals=[1]))
        mutated(lambda p:p['records'][fi].update(rule='hole'))
        for name, replacement in [('proof.alethe','(step evil (cl) :rule hole)\n'),
                                  ('lemma-0001.pac','m 7;\na 1 1;\nl 2 1*(1), 1;\nunsat\n')]:
            path=d/name; old=path.read_text();path.write_text(replacement)
            reject(lambda:pp.check_bundle(d,args.carcara,args.ffpacheck));rejected+=1
            path.write_text(old)
        # No variable declaration can accidentally provide the modulus check.
        constant=source('(assert (= (as ff2 F) (as ff0 F)))',3)
        proof=bp.produce(constant,args.z3,10)
        wrong=constant.replace('FiniteField 3','FiniteField 2')
        reject(lambda:bp.verify_export(wrong,proof));rejected+=1
        for text in [
            source('(assert (= a x))'),
            source('(assert (= (ite x x y) y))'),
            source('(assert (forall ((q F)) (= q q)))'),
            source('(assert (= x (f x)))',extra='(declare-fun f (F) F)'),
            source('(assert (= x z))',extra='(declare-const z (_ FiniteField 3))'),
            source('(push)\n(assert a)'),
            source('(check-sat)\n(assert false)'),
            source('(assert (= alias x))',extra='(define-fun alias () F alias)'),
        ]:
            reject(lambda:bp.Graph(text)); rejected+=1
        assert sat_count and unsat_count and sat_count+unsat_count+unknown_count==36
    print(json.dumps(dict(externally_checked=checked,rejected=rejected,
                          exhaustive_mixed=dict(sat=sat_count,unsat_certified=unsat_count,unsat_unavailable=unknown_count),
                          boolean_search_checks=search_checks,deep_let_depth=12000,sharing_chain=400)))


if __name__=='__main__': main()
