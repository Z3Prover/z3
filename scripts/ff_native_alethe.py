#!/usr/bin/env python3
"""Bounded Alethe elaboration of a supplied native proof (no field search).

The input assertions, native Boolean/equality proof and recorded PAC leaves are
one proof. Auxiliary polynomial variables are substituted by their original
terms or checked choice witnesses. Carcara checks the resulting original-input
proof; exact regeneration additionally binds PAC payloads, whose binding is not
checked by the pinned artifact's ff_pac rule.

Unsupported native steps fail closed. Small-field Fermat inputs are translated
to zero in Pacheck's finite-field quotient, without assuming a new input axiom.
"""
from pathlib import Path
import re
import z3
import ff_certificate as fc
import ff_boolean_proof as bp
import ff_native_evidence as ne
import ff_proof_pipeline as pp

require = fc.require


class NativeGraph(bp.Graph):
    def node(self, op, args=(), data=None):
        # Native clauses may contain a unary OR wrapper. Its SMT meaning is
        # exactly its child, including when nested inside a proof fact.
        if op in ('and', 'or') and len(args) < 2:
            return args[0] if args else super().node('true' if op == 'and' else 'false')
        return super().node(op, args, data)


class Exporter:
    def __init__(self, original, root):
        self.g = NativeGraph(original)
        self.w = bp.Writer(self.g)
        self.w.lines = []  # Emit all shared term definitions after elaboration.
        self.files, self.memo, self.counter = {}, {}, 0
        self.closed = {}
        self.ast_nodes, self.ast_pins = {}, []
        self.original = {i: None for i in self.g.assertions}
        for i in self.original:
            name = self.name('assertion')
            self.w.emit(f'(assume {name} {self.g.ref(i)})')
            self.original[i] = name
        require(z3.is_app(root) and z3.is_false(root.arg(root.num_args() - 1)), 'native root must prove false')
        self.root = root

    def name(self, kind):
        self.counter += 1
        require(self.counter < 50000, 'native export step limit')
        return f'{self.g.prefix}{kind}{self.counter}'

    def node(self, expr):
        # Read the typed AST directly. The pretty printer can flatten different
        # associative subterms depending on let-sharing, so its text must not
        # define equality of proof atoms. Pins prevent native AST-id reuse.
        pending = [expr]
        names = {z3.Z3_OP_TRUE:'true', z3.Z3_OP_FALSE:'false', z3.Z3_OP_NOT:'not',
                 z3.Z3_OP_AND:'and', z3.Z3_OP_OR:'or', z3.Z3_OP_IMPLIES:'=>',
                 z3.Z3_OP_XOR:'xor', z3.Z3_OP_ITE:'ite', z3.Z3_OP_EQ:'=',
                 z3.Z3_OP_FF_ADD:'ff.add', z3.Z3_OP_FF_MUL:'ff.mul', z3.Z3_OP_FF_NEG:'ff.neg'}
        while pending:
            e = pending[-1]; key = e.get_id()
            if key in self.ast_nodes: pending.pop(); continue
            require(z3.is_app(e), 'native term must be ground')
            missing = [a for a in e.children() if a.get_id() not in self.ast_nodes]
            if missing: pending.extend(missing); continue
            kind = e.decl().kind()
            if kind == z3.Z3_OP_UNINTERPRETED:
                require(e.num_args() == 0, 'native external profile excludes field-valued functions')
                name = fc.symbol(e.sexpr())
                require(name in self.g.names, 'native term has no original declaration')
                value = self.g.names[name]
            elif kind == z3.Z3_OP_FF_NUM:
                require(e.sort().size() == self.g.p, 'native field differs from original input')
                value = self.g.node('num', data=(e.as_long(), e.sort().size()))
            else:
                require(kind in names, 'unsupported native term operator: ' + str(e.decl().name()))
                value = self.g.node(names[kind], [self.ast_nodes[a.get_id()] for a in e.children()])
            self.ast_nodes[key] = value; self.ast_pins.append(e); pending.pop()
        return self.ast_nodes[expr.get_id()]

    def ref(self, expr):
        return self.g.ref(self.node(expr))

    def step(self, terms, rule, parents=(), args=None, **kw):
        return self.w.step(terms, rule, parents, args, **kw)

    def transfer(self, source, target, equality, premise):
        return self.w.transfer(source, target, equality, premise)

    def boolean(self, goal, parents=()):
        return self.boolean_ids(self.node(goal), [(self.node(f), name) for f, name in parents])

    def boolean_ids(self, goal, parents=()):
        """Elaborate a local propositional inference as checked resolution.

        Field equalities are opaque atoms. This cannot supply missing algebraic
        reasoning. Only native premise facts participate; no input is re-solved.
        """
        for fact, name in parents:
            if fact == goal: return name
        if self.g.nodes[goal][0] == 'true': return self.step(['true'], 'true')
        prefix = self.name('bool') + '_'
        atoms, asts = {}, []
        def term(i):
            op, args, _ = self.g.nodes[i]
            if op in ('true', 'false'): return op
            logical = op in ('and', 'or', 'not', '=>', 'xor') or op == 'ite' and self.g.typ(i) == 0
            logical |= op == '=' and self.g.typ(args[0]) == 0
            if logical:
                return '(' + op + ' ' + ' '.join(term(a) for a in args) + ')'
            if i not in atoms:
                require(len(atoms) < 4096, 'local Boolean atom limit')
                atoms[i] = prefix + 'atom' + str(len(atoms)); asts.append(i)
            return atoms[i]
        facts = [term(f) for f, _ in parents] + ['(not ' + term(goal) + ')']
        text = ''.join(f'(declare-const {n} Bool)\n' for n in atoms.values())
        text += ''.join('(assert ' + f + ')\n' for f in facts)
        g = bp.Graph(text); g.prefix = prefix
        # Substitute the actual opaque atom terms in the printed proof. Their
        # truth values remain unconstrained throughout propositional search.
        for a in asts:
            i = g.names[atoms[a]]
            g.nodes[i] = ('var', (), (self.g.ref(a), 0))
        base = bp.Clauses(g)
        search = bp.Search(base.clauses)
        sat, root = search.search()
        require(not sat, 'native step needs non-propositional evidence: ' + self.g.ref(goal))
        writer = bp.Writer(g)
        anchor = self.name('boolean_lemma')
        writer.emit(f'(anchor :step {anchor})')
        writer.base(base)
        # Parent facts already have proofs in the enclosing scope; only the
        # negation of the desired conclusion is a new local assumption.
        for i, (_, name) in enumerate(parents):
            old = f'{g.prefix}a{i}'
            writer.lines = [line for line in writer.lines if not line.startswith(f'(assume {old} ')]
            writer.names[i] = name
        for record in search.records:
            a, b, pivot = record['left'], record['right'], record['pivot']
            value = bp.resolve(search.clauses[a], search.clauses[b], pivot)
            writer.names.append(writer.step([g.literal(x) for x in value], 'resolution',
                                            [writer.names[a], writer.names[b]]))
        writer.step([], 'reordering', [writer.names[root]])
        target = self.g.ref(goal)
        assumption = f'{g.prefix}a{len(parents)}'
        writer.step([f'(not (not {target}))', 'false'], 'subproof', name=anchor, discharge=[assumption])
        outside_false = writer.step(['(not false)'], 'false')
        double = writer.step([f'(not (not {target}))'], 'resolution', [anchor, outside_false])
        simple = writer.step([f'(= (not (not {target})) {target})'], 'not_simplify')
        result = writer.transfer(f'(not (not {target}))', target, simple, double)
        for line in writer.lines: self.w.emit(line)
        return result

    def rewrite(self, goal):
        # Equality symmetry is independent of the size or meaning of its
        # operands. Expanding a shared circuit just to exchange the two sides
        # can be exponential; the standard Alethe rule checks the exact swap.
        if z3.is_eq(goal):
            left, right = goal.children()
            if left.eq(right):
                return self.step([self.ref(goal)], 'refl')
            if z3.is_eq(left) and z3.is_eq(right) and left.arg(0).eq(right.arg(1)) and left.arg(1).eq(right.arg(0)):
                return self.step([self.ref(goal)], 'eq_symmetric')
        # First try the propositional rewrite with field equalities treated as
        # opaque atoms. Their reflexivity and symmetry need no polynomial
        # expansion, even when nested below not/and/ite. Every added bridge is
        # checked by an ordinary Alethe equality rule.
        simple, todo, visited = [], [goal], set()
        while todo:
            e = todo.pop()
            if e.get_id() in visited: continue
            visited.add(e.get_id())
            if z3.is_eq(e) and isinstance(e.arg(0).sort(), z3.FiniteFieldSortRef):
                a, b = e.children()
                if a.eq(b):
                    simple.append((e, self.step([self.ref(e)], 'refl')))
                elif a.get_id() > b.get_id():
                    bridge = e == (b == a)
                    simple.append((bridge, self.step([self.ref(bridge)], 'eq_symmetric')))
            else:
                todo.extend(a for a in e.children() if z3.is_bool(a))
        try:
            return self.boolean(goal, simple)
        except fc.Invalid:
            # Algebraic rewrites still require the bounded ring normalization
            # below. A failed propositional search supplies no proof premise.
            pass
        # Normalize each field equality with an explicit nonzero scaling
        # identity. The residual transformation is purely propositional.
        parents, pending, seen, variables, cache = [], [goal], set(), {}, {}
        def polynomial(e, ar):
            key = e.get_id()
            if key in cache: return cache[key]
            k = e.decl().kind()
            if k == z3.Z3_OP_FF_NUM:
                value = {(): e.as_long()} if e.as_long() else {}
            elif k in ne.OPS:
                value = {(): 1} if k == z3.Z3_OP_FF_MUL else {}
                for i, a in enumerate(e.children()):
                    child = polynomial(a, ar)
                    value = ar.mul(value, child) if k == z3.Z3_OP_FF_MUL else ar.add(
                        value, child, -1 if k == z3.Z3_OP_FF_NEG else pow(2, i, ar.p) if k == z3.Z3_OP_FF_BITSUM else 1)
            else:
                if key not in variables: variables[key] = (len(variables), e)
                value = {(variables[key][0],): 1}
            cache[key] = value
            return value
        while pending:
            e = pending.pop()
            if e.get_id() in seen: continue
            seen.add(e.get_id())
            if not (z3.is_eq(e) and isinstance(e.arg(0).sort(), z3.FiniteFieldSortRef)):
                pending.extend(a for a in e.children() if z3.is_bool(a)); continue
            a, b = e.children(); field = a.sort(); ar = fc.Arithmetic(field.size())
            if z3.is_app_of(a, z3.Z3_OP_ITE) or z3.is_app_of(b, z3.Z3_OP_ITE):
                choices = [[(t.arg(0), t.arg(1)), (z3.Not(t.arg(0)), t.arg(2))]
                           if z3.is_app_of(t, z3.Z3_OP_ITE) else [(None, t)] for t in (a, b)]
                for ca, va in choices[0]:
                    for cb, vb in choices[1]:
                        selections = [(t, c, v) for t, c, v in [(a, ca, va), (b, cb, vb)] if c is not None]
                        assumptions = [c for _, c, _ in selections]
                        branch_eq = va == vb
                        bridge = e == branch_eq
                        anchor = self.name('ite_equality')
                        self.w.emit(f'(anchor :step {anchor})')
                        names, equalities = [], []
                        for _, c, _ in selections:
                            name = self.name('selector'); names.append(name)
                            self.w.emit(f'(assume {name} {self.ref(c)})')
                        for (t, c, v), name in zip(selections, names):
                            axiom = z3.Or(z3.Not(c), t == v)
                            selected = self.boolean(t == v, [(c, name), (axiom, self.ite_axiom(axiom))])
                            equalities.append(selected)
                        proved = self.step([self.ref(bridge)], 'cong', equalities)
                        self.step([f'(not {self.ref(c)})' for c in assumptions] + [self.ref(bridge)],
                                  'subproof', name=anchor, discharge=names)
                        clause = z3.Or(*[z3.Not(c) for c in assumptions], bridge)
                        folds = [self.step([self.ref(clause), f'(not {self.ref(lit)})'], 'or_neg', args=[str(i)])
                                 for i, lit in enumerate(list(clause.children()))]
                        unit = self.step([self.ref(clause)], 'resolution', [anchor] + folds)
                        parents.append((clause, unit)); pending.append(branch_eq)

            value = ar.add(polynomial(a, ar), polynomial(b, ar), -1)
            scale = pow(value[sorted(value)[0]], -1, ar.p) if value else 1
            value = ar.mul(value, {(): scale})
            vs = {i: v for i, v in variables.values()}
            pieces = []
            for mon, coeff in sorted(value.items()):
                product = z3.FiniteFieldVal(coeff, field)
                for v in mon: product = product * vs[v]
                pieces.append(product)
            poly = z3.FiniteFieldVal(0, field)
            for piece in pieces: poly = poly + piece
            canonical = poly == z3.FiniteFieldVal(0, field)
            zero, one = f'(as ff0 {bp.sort_text(ar.p)})', f'(as ff1 {bp.sort_text(ar.p)})'
            scale_text = f'(as ff{scale} {bp.sort_text(ar.p)})'
            identity = self.step([f'(= (ff.mul {scale_text} (ff.add {self.ref(a)} (ff.neg {self.ref(b)}))) '
                                  f'(ff.mul {one} (ff.add {self.ref(poly)} (ff.neg {zero}))))'], 'poly_simp')
            equivalence = self.step([f'(= {self.ref(e)} {self.ref(canonical)})'], 'poly_simp_rel', [identity])
            parents.append((e == canonical, equivalence))
            if not value or set(value) == {()}:
                # Constant field equality: poly_simp first removes arithmetic,
                # then eq_simplify checks the two literal constants.
                constant = z3.FiniteFieldVal(value.get((), 0), field)
                reduced = constant == z3.FiniteFieldVal(0, field)
                ident = self.step([self.ref(poly == constant)], 'poly_simp')
                eq = self.step([self.ref(canonical == reduced)], 'cong', [ident])
                parents.append((canonical == reduced, eq))
                if not value:
                    proved = self.step([self.ref(reduced)], 'refl')
                    parents.append((reduced, proved))
                else:
                    proved = self.constant_disequality(reduced)
                    parents.append((z3.Not(reduced), proved))
        try:
            return self.boolean(goal, parents)
        except fc.Invalid as error:
            raise fc.Invalid(str(error) + ': ' + goal.sexpr()[:1200]) from error

    def constant_disequality(self, equation):
        # Carcara's generic eq_simplify does not evaluate finite-field
        # constants. Elaborate c != 0 as the one-step PAC inference c/c = 1;
        # the input equality is a discharged hypothesis, never an axiom.
        a, b = equation.children()
        require(a.decl().kind() == z3.Z3_OP_FF_NUM and b.decl().kind() == z3.Z3_OP_FF_NUM
                and b.as_long() == 0 and a.as_long() != 0, 'constant disequality profile')
        p, c = a.sort().size(), a.as_long()
        anchor, assumption = self.name('constant_lemma'), self.name('constant_assumption')
        self.w.emit(f'(anchor :step {anchor})')
        self.w.emit(f'(assume {assumption} {self.ref(equation)})')
        converted = self.step([f'(not (set.is_empty (@ff.variety (@ff.ideal {self.ref(a)}))))'],
                              'ff_poly_conversion', [assumption])
        pac = f'm {p};\na 1 {c};\nl 2 1*({pow(c,-1,p)}), 1;\nunsat\n'
        self.step([], 'ff_pac', [converted], [pac])
        self.files[anchor + '.pac'] = pac
        self.step([f'(not {self.ref(equation)})', 'false'], 'subproof', name=anchor, discharge=[assumption])
        false = self.step(['(not false)'], 'false')
        return self.step([f'(not {self.ref(equation)})'], 'resolution', [anchor, false])

    def ite_axiom(self, goal):
        pending, seen, parents = [goal], set(), []
        while pending:
            e = pending.pop()
            if e.get_id() in seen: continue
            seen.add(e.get_id()); pending.extend(e.children())
            if z3.is_app_of(e, z3.Z3_OP_ITE) and not z3.is_bool(e):
                c, a, b = e.children()
                meaning = z3.If(c, e == a, e == b)
                target = self.ref(meaning)
                truth = self.step(['true'], 'true')
                identity = self.step([f'(= true (and true {target}))'], 'ite_intro')
                conj = self.transfer('true', f'(and true {target})', identity, truth)
                proved = self.step([target], 'and', [conj], ['1'])
                parents.append((meaning, proved))
                for branch in [a, b]:
                    symmetric = (e == branch) == (branch == e)
                    parents.append((symmetric, self.step([self.ref(symmetric)], 'eq_symmetric')))
        return self.boolean(goal, parents)

    def fold_clause(self, assumptions, anchor):
        literals = [z3.Not(a) for a in assumptions]
        ctx = self.root.ctx
        clause = literals[0] if len(literals) == 1 else z3.Or(*literals) if literals else z3.BoolVal(False, ctx=ctx)
        clause_text = self.ref(clause)
        false = self.step(['(not false)'], 'false')
        if len(literals) < 2:
            unit = self.step([clause_text], 'resolution', [anchor, false]) if literals else self.step(['false'], 'reordering', [anchor])
        else:
            negs = [self.step([clause_text, f'(not (not {self.ref(a)}))'], 'or_neg', args=[str(i)])
                    for i,a in enumerate(assumptions)]
            unit = self.step([clause_text], 'resolution', [anchor, false] + negs)
        return clause, unit

    def field(self, proof):
        problem, dag, bindings, origins, cert, values = ne.replay_lemma(proof)
        evidence = proof.decl().params()[2]
        p = int(cert[':modulus']); sort = bp.sort_text(p)
        zero, one = f'(as ff0 {sort})', f'(as ff1 {sort})'
        assumptions = evidence.arg(0).children()
        anchor = self.name('field_lemma')
        self.w.emit(f'(anchor :step {anchor})')
        names = []
        for a in assumptions:
            name = self.name('field_assumption'); names.append(name)
            self.w.emit(f'(assume {name} {self.ref(a)})')
        witnesses = {}
        mapped = []
        for binding in bindings:
            if isinstance(binding, tuple):
                _, eq = binding; a, b = map(self.ref, eq.children())
                binder = self.name('inverse')
                choice = f'(choice (({binder} {sort})) (= (ff.mul {binder} (ff.add {a} (ff.neg {b}))) {one}))'
                witnesses[eq.get_id()] = choice; mapped.append(choice)
            else: mapped.append(self.ref(binding))
        proofs, normalized, polys = [], [], []
        # Pacheck checks arithmetic modulo v^p=v. Each native Fermat input
        # is therefore zero in its proof language. Replace only those inputs
        # whose native origin was independently verified by ne.encode; all
        # other inputs retain their exact polynomial. The unchanged inference
        # DAG is checked by Pacheck in that quotient, including final closure.
        cert = dict(cert)
        cert[':inputs'] = [[] if origin == 'fermat' else raw
                           for raw, origin in zip(cert[':inputs'], origins)]
        for raw, origin in zip(cert[':inputs'], origins):
            value = fc.decode_polynomial(raw, fc.Arithmetic(p), len(mapped))
            poly = fc.sexpr(fc.polynomial_term(value, p, mapped)); polys.append(poly)
            canonical = f'(= {poly} {zero})'; normalized.append(canonical)
            if origin is None or origin == 'fermat':
                # Definitions are identities after substituting original terms.
                proofs.append(self.step([canonical], 'poly_simp')); continue
            lit, name = assumptions[origin], names[origin]
            eq = lit.arg(0) if z3.is_not(lit) else lit
            a, b = map(self.ref, eq.children()); equation = self.ref(lit)
            if z3.is_not(lit):
                choice = witnesses[eq.get_id()]
                value_text = f'(ff.add (ff.mul (ff.add {a} (ff.neg {b})) {choice}) (as ff{p-1} {sort}))'
                positive = f'(= {value_text} {zero})'
                conversion = self.step([f'(= {equation} {positive})'], 'ff_diseq', args=[a,b,choice])
                name = self.transfer(equation, positive, conversion, name)
                equation, a, b = positive, value_text, zero
            identity = self.step([f'(= (ff.mul {one} (ff.add {a} (ff.neg {b}))) '
                                  f'(ff.mul {one} (ff.add {poly} (ff.neg {zero}))))'], 'poly_simp')
            equivalence = self.step([f'(= {equation} {canonical})'], 'poly_simp_rel', [identity])
            proofs.append(self.transfer(equation, canonical, equivalence, name))
        conj = proofs[0] if len(proofs) == 1 else self.step(['(and ' + ' '.join(normalized) + ')'], 'and_intro', proofs)
        conversion = self.step(['(not (set.is_empty (@ff.variety (@ff.ideal ' + ' '.join(polys) + '))))'], 'ff_poly_conversion', [conj])
        pac = pp.export_pac(cert, values)
        # The payload is a string literal, as in the artifact's existing bridge.
        self.step([], 'ff_pac', [conversion], [pac])
        self.files[anchor + '.pac'] = pac
        discharged = [f'(not {self.ref(a)})' for a in assumptions] + ['false']
        self.step(discharged, 'subproof', name=anchor, discharge=names)
        # Convert the derived clause to the native lemma's (possibly weakened)
        # Boolean fact through an explicit propositional inference.
        clause, unit = self.fold_clause(assumptions, anchor)
        return self.boolean(proof.arg(0), [(clause, unit)])

    def unit_resolution(self, fact, parents):
        # Most native SAT steps already are Alethe resolution. Preserve that
        # trace directly instead of rebuilding a local Tseitin proof per step.
        # First check the literal sets; unusual native weakening still goes
        # through the bounded propositional elaborator below.
        if len(parents) < 2: return self.boolean(fact, parents)
        first, first_name = parents[0]
        lit = lambda e: self.g.lit(self.node(e))
        direct = len(parents) == 2 and lit(first) == -lit(parents[1][0])
        atoms = list(first.children()) if z3.is_or(first) and not direct else [first]
        residual = set(map(lit, atoms))
        for value, _ in parents[1:]:
            if -lit(value) not in residual: return self.boolean(fact, parents)
            residual.remove(-lit(value))
        desired = [] if z3.is_false(fact) else list(fact.children()) if z3.is_or(fact) else [fact]
        if residual != set(map(lit, desired)): return self.boolean(fact, parents)
        premise = self.step([self.ref(a) for a in atoms], 'or', [first_name]) if z3.is_or(first) and not direct else first_name
        clause = self.step([self.ref(a) for a in desired], 'resolution', [premise] + [name for _,name in parents[1:]])
        if not desired: return self.step(['false'], 'weakening', [clause])
        if len(desired) == 1: return clause
        target = self.ref(fact)
        folds = [self.step([target, f'(not {self.ref(a)})'], 'or_neg', args=[str(i)]) for i,a in enumerate(desired)]
        return self.step([target], 'resolution', [clause] + folds)

    def convert(self, proof, env=None, depth=0):
        env = {} if env is None else env
        require(depth < 256, 'native proof nesting limit')
        key = (proof.get_id(), () if self.closed.get(proof.get_id(), False) else tuple(sorted(env.items())))
        if key in self.memo: return self.memo[key]
        kind = proof.decl().kind(); fact = proof.arg(proof.num_args() - 1)
        if kind == z3.Z3_OP_PR_ASSERTED:
            i = self.node(fact)
            if i in self.original:
                result = self.original[i]
            else:
                # Z3's assertion pipeline flattens nested Boolean conjunctions
                # before recording PR_ASSERTED. Derive that version from the
                # actual SMT input, rather than promoting it to an assumption.
                field_atoms = {}
                signatures = {}
                def shape(n):
                    if n in signatures: return signatures[n]
                    op, args, _ = self.g.nodes[n]
                    if op in ('and', 'or', 'ff.add', 'ff.mul'):
                        flat, todo = [], list(args)
                        while todo:
                            child = todo.pop()
                            if self.g.nodes[child][0] == op: todo.extend(self.g.nodes[child][1])
                            else: flat.append(shape(child))
                        value = (op, tuple(sorted(flat)))
                    elif args:
                        value = (op, tuple(shape(a) for a in args))
                    else: value = ('atom', n)
                    if self.g.field_atom(n): field_atoms.setdefault(value, set()).add(n)
                    signatures[n] = value
                    return value
                signature = shape(i)
                matching = [j for j in self.original if shape(j) == signature]
                require(matching, 'native assertion is absent from original input')
                j = matching[0]
                parents = [(j, self.original[j])]
                for atoms in field_atoms.values():
                    atoms = sorted(atoms)
                    for a, b in zip(atoms, atoms[1:]):
                        left, right = self.g.nodes[a][1], self.g.nodes[b][1]
                        one = f'(as ff1 {bp.sort_text(self.g.p)})'
                        identity = self.step([f'(= (ff.mul {one} (ff.add {self.g.ref(left[0])} (ff.neg {self.g.ref(left[1])}))) '
                                              f'(ff.mul {one} (ff.add {self.g.ref(right[0])} (ff.neg {self.g.ref(right[1])}))))'], 'poly_simp')
                        equality = self.g.node('=', (a,b))
                        proved = self.step([self.g.ref(equality)], 'poly_simp_rel', [identity])
                        parents.append((equality, proved))
                result = self.boolean_ids(i, parents)
        elif kind == z3.Z3_OP_PR_HYPOTHESIS:
            require(fact.get_id() in env, 'open native hypothesis')
            result = env[fact.get_id()]
        elif kind == z3.Z3_OP_PR_TH_LEMMA:
            result = self.field(proof)
        elif kind == z3.Z3_OP_PR_LEMMA:
            hypotheses, todo, seen = {}, [proof.arg(0)], set()
            while todo:
                node = todo.pop()
                if node.get_id() in seen: continue
                seen.add(node.get_id())
                if node.decl().kind() == z3.Z3_OP_PR_LEMMA: continue
                if node.decl().kind() == z3.Z3_OP_PR_HYPOTHESIS:
                    h = node.arg(0); hypotheses[h.get_id()] = h
                else: todo.extend(node.children()[:-1])
            anchor = self.name('native_lemma'); self.w.emit(f'(anchor :step {anchor})')
            local, names = dict(env), []
            for i,h in hypotheses.items():
                name = self.name('hypothesis'); names.append(name); local[i] = name
                self.w.emit(f'(assume {name} {self.ref(h)})')
            contradiction = self.convert(proof.arg(0), local, depth + 1)
            false = self.step(['(not false)'], 'false')
            self.step([], 'resolution', [contradiction, false])
            self.step([f'(not {self.ref(h)})' for h in hypotheses.values()] + ['false'],
                      'subproof', name=anchor, discharge=names)
            clause, unit = self.fold_clause(list(hypotheses.values()), anchor)
            result = self.boolean(fact, [(clause, unit)])
        else:
            parents = [(p.arg(p.num_args()-1), self.convert(p, env, depth + 1)) for p in proof.children()[:-1]]
            rules = {z3.Z3_OP_PR_REFLEXIVITY:'refl', z3.Z3_OP_PR_SYMMETRY:'symm',
                     z3.Z3_OP_PR_TRANSITIVITY:'trans', z3.Z3_OP_PR_TRANSITIVITY_STAR:'trans',
                     z3.Z3_OP_PR_MONOTONICITY:'cong'}
            if kind in rules:
                result = self.step([self.ref(fact)], rules[kind], [name for _,name in parents])
            elif kind in (z3.Z3_OP_PR_REWRITE, z3.Z3_OP_PR_COMMUTATIVITY) and z3.is_eq(fact) and not z3.is_bool(fact.arg(0)):
                lhs, rhs = fact.children()
                if z3.is_app_of(lhs, z3.Z3_OP_ITE) and (
                        z3.is_true(lhs.arg(0)) and lhs.arg(1).eq(rhs) or
                        z3.is_false(lhs.arg(0)) and lhs.arg(2).eq(rhs) or
                        lhs.arg(1).eq(lhs.arg(2)) and lhs.arg(1).eq(rhs) or
                        z3.is_not(lhs.arg(0)) and z3.is_app_of(rhs, z3.Z3_OP_ITE) and
                        lhs.arg(0).arg(0).eq(rhs.arg(0)) and lhs.arg(1).eq(rhs.arg(2)) and lhs.arg(2).eq(rhs.arg(1))):
                    result = self.step([self.ref(fact)], 'ite_simplify')
                else:
                    result = self.step([self.ref(fact)], 'poly_simp')
            elif kind in (z3.Z3_OP_PR_REWRITE, z3.Z3_OP_PR_COMMUTATIVITY):
                require(not parents, 'rewrite with parents')
                result = self.rewrite(fact)
            elif kind == z3.Z3_OP_PR_UNIT_RESOLUTION:
                result = self.unit_resolution(fact, parents)
            elif kind == z3.Z3_OP_PR_MODUS_PONENS and len(parents) == 2 and z3.is_eq(parents[1][0]) and parents[0][0].eq(parents[1][0].arg(0)) and fact.eq(parents[1][0].arg(1)):
                result = self.transfer(self.ref(parents[0][0]), self.ref(fact), parents[1][1], parents[0][1])
            elif kind in (z3.Z3_OP_PR_AND_ELIM, z3.Z3_OP_PR_NOT_OR_ELIM) and len(parents) == 1:
                source, name = parents[0]
                parts = source.arg(0).children() if kind == z3.Z3_OP_PR_NOT_OR_ELIM and z3.is_not(source) and z3.is_or(source.arg(0)) else source.children() if z3.is_and(source) else []
                expected = fact.arg(0) if kind == z3.Z3_OP_PR_NOT_OR_ELIM and z3.is_not(fact) else fact
                index = next((i for i,a in enumerate(parts) if a.eq(expected)), None)
                result = self.boolean(fact, parents) if index is None else self.step([self.ref(fact)], 'and' if kind == z3.Z3_OP_PR_AND_ELIM else 'not_or', [name], [str(index)])
            elif kind == z3.Z3_OP_PR_DEF_AXIOM:
                require(not parents, 'Boolean axiom with parents')
                result = self.ite_axiom(fact)
            elif kind in [z3.Z3_OP_PR_MODUS_PONENS, z3.Z3_OP_PR_UNIT_RESOLUTION,
                          z3.Z3_OP_PR_AND_ELIM, z3.Z3_OP_PR_NOT_OR_ELIM,
                          z3.Z3_OP_PR_IFF_TRUE, z3.Z3_OP_PR_IFF_FALSE,
                          z3.Z3_OP_PR_REWRITE]:
                result = self.boolean(fact, parents)
            else: raise fc.Invalid('unsupported native proof rule: ' + str(proof.decl().name()))
        self.memo[key] = result
        return result

    def export(self):
        # Emit closed native subproofs in the outer scope before any consumer
        # opens an anchor. Reusing a step created inside a sibling anchor would
        # violate Alethe scope, even if the underlying theorem is closed.
        # Open proofs retain the full hypothesis environment in their cache key.
        pending, ordered = [self.root], []
        while pending:
            node = pending[-1]; key = node.get_id()
            if key in self.closed:
                pending.pop(); continue
            require(len(self.closed) < 100000, 'native proof DAG node limit')
            parents = node.children()[:-1]
            missing = [p for p in parents if p.get_id() not in self.closed]
            if missing:
                pending.extend(missing); continue
            kind = node.decl().kind()
            self.closed[key] = kind == z3.Z3_OP_PR_LEMMA or (
                kind != z3.Z3_OP_PR_HYPOTHESIS and all(self.closed[p.get_id()] for p in parents))
            ordered.append(node); pending.pop()
        for node in ordered:
            if self.closed[node.get_id()]: self.convert(node)
        root = self.convert(self.root)
        false = self.step(['(not false)'], 'false')
        self.step([], 'resolution', [root, false])
        self.files['proof.alethe'] = '\n'.join(self.g.definitions() + self.w.lines) + '\n'
        require(sum(len(t.encode()) for t in self.files.values()) <= pp.LIMIT, 'native bundle size limit')
        return self.files


def artifacts(original, root):
    return Exporter(original, root).export()


def _check_bundle(original, root, directory, carcara, ffpacheck, timeout, create):
    import time
    deadline = time.monotonic() + timeout
    def remaining():
        seconds = deadline - time.monotonic()
        require(seconds > 0, 'native whole-proof checking timeout')
        return seconds
    directory = Path(directory)
    if create:
        directory.mkdir(parents=True, exist_ok=False)
        (directory/'problem.smt2').write_text(original)
    require((directory/'problem.smt2').read_text() == original, 'original input changed')
    files = artifacts(original, root)
    for name, expected in files.items():
        if create:
            (directory/name).write_text(expected)
        require((directory/name).read_text() == expected, 'native whole-proof binding mismatch: ' + name)
    runs = []
    for name in files:
        if not name.endswith('.pac'): continue
        result = pp.run([str(ffpacheck), str(directory/name)], remaining())
        output = re.sub(r'\x1b\[[0-9;]*m', '', result['stdout'])
        require('PROOF CHECK: SUCCEEDED' in [s.strip() for s in output.splitlines()], 'PAC completion marker missing')
        runs.append(result)
    result = pp.run([str(carcara), 'check', str(directory/'proof.alethe'), str(directory/'problem.smt2'),
                     '--expand-let-bindings', '--apply-function-defs', '--ff-pac-solver', str(ffpacheck)], remaining())
    require(result['stdout'].strip() == 'valid', 'Alethe completion marker missing')
    return {'carcara':result, 'pac':runs}, files


def check_bundle(original, root, directory, carcara, ffpacheck, timeout=10):
    """Reconstruct the binding from the original input and proof, then check files."""
    return _check_bundle(original, root, directory, carcara, ffpacheck, timeout, False)[0]


def write_and_check_bundle(original, root, directory, carcara, ffpacheck, timeout=10):
    """Create a fresh bundle with one binding/replay pass and all external checks.

    The expected contents are computed here, never supplied by the producer.
    Existing bundles must use check_bundle, which independently reconstructs
    their contents and rejects modifications before invoking either checker.
    """
    return _check_bundle(original, root, directory, carcara, ffpacheck, timeout, True)


def main():
    import argparse
    import json
    import time
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--out', type=Path, required=True, help='new output directory')
    parser.add_argument('--carcara', type=Path, required=True)
    parser.add_argument('--ffpacheck', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=10, help='whole-pipeline time budget in seconds')
    args = parser.parse_args()
    require(args.timeout > 0, 'timeout must be positive')
    original = pp.read(args.input)
    started = time.monotonic()
    ctx = z3.Context(proof=True)
    solver = z3.Solver(ctx=ctx)
    solver.set(timeout=max(1, int(args.timeout * 1000)))
    solver.from_string(original)
    require(solver.check() == z3.unsat, 'native solver did not produce UNSAT')
    root = solver.proof()
    remaining = args.timeout - (time.monotonic() - started)
    require(remaining > 0, 'whole-pipeline timeout before external checking')
    checks, files = write_and_check_bundle(original, root, args.out, args.carcara, args.ffpacheck, remaining)
    elapsed = time.monotonic() - started
    require(elapsed <= args.timeout, 'whole-pipeline timeout')
    receipt = {'status':'checked', 'profile':'native whole-proof Alethe/PAC',
               'z3_version':z3.get_version_string(), 'seconds':elapsed,
               'files':{name:pp.digest(args.out/name) for name in ['problem.smt2'] + list(files)},
               'checks':checks}
    (args.out/'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ['files', 'checks']}))


if __name__ == '__main__':
    try:
        main()
    except (fc.Invalid, z3.Z3Exception, OSError, RecursionError) as error:
        import sys
        print('native Alethe proof not checked: ' + str(error), file=sys.stderr)
        sys.exit(1)
