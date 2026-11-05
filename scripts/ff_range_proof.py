"""Experimental, bounded circuit range lemmas; every lemma carries a PAC proof.

Names, ordering and asserted polarity do not establish facts. Matching only
proposes conditional lemmas to the untrusted algebra engine. The ordinary
original-input checker must reconstruct and validate every retained inference.
"""
import time
from types import SimpleNamespace

# Search bounds limit preprocessing cost; exceeding them drops opportunities,
# never changes the meaning of the original input or admits an unchecked fact.
MAX_SEEDS = 512
MAX_SUM = 16


def augment(g, compounds=False):
    if not g.ites or g.source_nodes > 5000:
        return
    zero = g.node('num', data=(0, g.p))
    def num(n): return g.node('num', data=(n % g.p, g.p))
    def eq(a, b):
        return g.intern.get(('=', (b, a), None)) or g.node('=', (a, b))
    def mul(*a): return g.node('ff.mul', a)
    def add(*a): return g.node('ff.add', a)
    def domain(x, k):
        # R_k(x)=0 states membership in {0,...,k}; no order on F_p is assumed.
        factors = [x] + [add(x, num(-j)) for j in range(1, k+1)]
        return eq(mul(*factors), zero)
    def seed(*lits):
        if len(g.range_seeds) < MAX_SEEDS and len(set(map(abs, lits))) == len(lits):
            value = tuple(lits)
            if value not in seen: seen.add(value); g.range_seeds.append(value)
    seen = set()
    bits = {}
    equalities = [i for i in range(1, g.source_nodes) if g.field_atom(i)]
    if len(equalities) > 256: return
    # Either selected ITE value is a root of x(x-1). Boolean ITE clauses
    # supply the selected equality, so no assignment to its condition is needed.
    for i, _ in g.ites:
        _, (condition, a, b), _ = g.nodes[i]
        if {g.nodes[x][2][0] % g.p for x in (a,b) if g.nodes[x][0] == 'num'} != {0,1}: continue
        bits[i] = domain(i, 1)
        for v in (0,1): seed(eq(i,num(v)), -bits[i])
    # Each equality remains a premise, including those under disjunction/negation.
    for atom in equalities:
        a,b = g.nodes[atom][1]
        if a in bits: a,b = b,a
        if b not in bits or g.nodes[a][0] != 'var': continue
        bits[a] = domain(a,1)
        seed(atom, bits[b], -bits[a])
        for v in (0,1):
            seed(atom, eq(b,num(v)), -eq(a,num(v)))
            seed(atom, eq(a,num(v)), -eq(b,num(v)))

    def complement(x,y):
        op,args,_ = g.nodes[x]
        if op != 'ff.add' or len(args) != 2: return False
        for c,t in (args, args[::-1]):
            if g.nodes[c][0] != 'num' or g.nodes[c][2][0] % g.p != 1: continue
            op2,a2,_ = g.nodes[t]
            if op2 == 'ff.neg' and a2 == (y,): return True
            if op2 == 'ff.mul' and len(a2) == 2:
                for v,k in (a2,a2[::-1]):
                    if v == y and g.nodes[k][0] == 'num' and g.nodes[k][2][0] % g.p == g.p-1: return True
        return False

    gates = []
    for atom in equalities:
        for product,y in (g.nodes[atom][1],g.nodes[atom][1][::-1]):
            op,args,_ = g.nodes[product]
            if op != 'ff.mul' or len(args) != 2 or g.typ(y) != g.p: continue
            for s,w in (args,args[::-1]):
                if g.nodes[s][0] != 'ff.add' or g.nodes[w][0] != 'var': continue
                for other in equalities:
                    for prod,z in (g.nodes[other][1],g.nodes[other][1][::-1]):
                        if g.nodes[z][0] != 'num' or g.nodes[z][2][0] % g.p: continue
                        op2,terms,_ = g.nodes[prod]
                        if op2 != 'ff.mul' or len(terms) != 2: continue
                        if not any(t == s and (complement(c,y) or complement(y,c)) for t,c in (terms,terms[::-1])): continue
                        gates.append((s,y,atom,other))
    # y=w*S and (1-y)*S=0 imply y(1-y)=w*S*(1-y)=0.
    # S=0 forces y=0; S!=0 forces y=1 by cancellation in the field.
    for s,y,a,b in gates:
        bits[y] = domain(y,1)
        seed(a,b,-bits[y])
        seed(a,eq(s,zero),-eq(y,zero))
        seed(b,-eq(s,zero),-eq(y,num(1)))
        seed(b,eq(y,zero),-eq(s,zero))
        seed(a,eq(y,num(1)),eq(s,zero))

    # Complements, products and aliases transmit bit domains and value facts.
    # If x is a bit, so is 1-x. Products of bits are bits, equal to one
    # exactly when all factors are one. Substitution across an equality always
    # retains that equality as a premise. Each implication is proved separately.
    for _ in range(8):
        before = len(bits)
        for x in range(1, g.source_nodes):
            if x in bits or g.typ(x) != g.p: continue
            op,args,_ = g.nodes[x]
            parents = [v for v in bits if complement(x,v) or complement(v,x)]
            if parents:
                v = parents[0]; bits[x] = domain(x,1)
                seed(bits[v],-bits[x])
                for k in (0,1):
                    seed(eq(v,num(k)),-eq(x,num(1-k)))
                    seed(eq(x,num(k)),-eq(v,num(1-k)))
            elif op == 'ff.mul' and 2 <= len(args) <= 8 and all(v in bits for v in args):
                bits[x] = domain(x,1)
                seed(*(bits[v] for v in args),-bits[x])
                seed(*(eq(v,num(1)) for v in args),-eq(x,num(1)))
                for v in args:
                    seed(eq(v,zero),-eq(x,zero))
                    seed(bits[v],eq(x,num(1)),-eq(v,num(1)))
        for atom in equalities:
            for x,v in (g.nodes[atom][1],g.nodes[atom][1][::-1]):
                if v not in bits or x in bits or g.nodes[x][0] != 'var': continue
                bits[x] = domain(x,1); seed(atom,bits[v],-bits[x])
                for k in (0,1):
                    seed(atom,eq(v,num(k)),-eq(x,num(k)))
                    seed(atom,eq(x,num(k)),-eq(v,num(k)))
        if compounds:
            import ff_circuit_proof
            for x in range(1,g.source_nodes):
                op,args,_=g.nodes[x]
                if x in bits or op!='ff.add' or len(args)>4: continue
                matched=ff_circuit_proof.regroup(g,x,bits,equalities,g.node,num,eq,domain,seed)
                if matched is None or len(matched[0])!=1 or x in bits: continue
                (value,),premises=matched
                bits[x]=domain(x,1)
                # The regrouped term is a bit only under the original wire
                # equations. Preserve those premises in each domain/value lemma.
                seed(*premises,bits[value],-bits[x])
                for v in (0,1):
                    seed(*premises,eq(value,num(v)),-eq(x,num(v)))
                    seed(*premises,eq(x,num(v)),-eq(value,num(v)))
        if len(bits) == before: break

    # A cut is a conservative definition, not a fresh unconstrained assertion.
    # Keeping partial sums opaque inside each PAC query bounds its dimension;
    # Alethe expands the same definitions when checking the refl identities.
    def cut(expr):
        i = g.node('var', data=(g.prefix+'cut'+str(len(g.nodes)),g.p))
        g.cut_definitions[i] = expr
        return i,eq(i,expr)
    sums = {}
    def tree(leaves):
        if len(leaves) == 1: return leaves[0],1,bits[leaves[0]],[]
        split = len(leaves)//2
        a,ka,ra,da = tree(leaves[:split]); b,kb,rb,db = tree(leaves[split:])
        c,definition = cut(add(a,b)); k=ka+kb; rc=domain(c,k)
        # On the finite grid a in [0,ka], b in [0,kb], their sum is a root
        # of R_(ka+kb), including modular wrap. The native producer must supply
        # the polynomial identity; the independent checker replays it.
        seed(ra,rb,definition,-rc)
        # With k<p, the only representatives in these ranges summing to zero
        # are both zero. The certificate proves this polynomial consequence.
        if k < g.p:
            seed(ra,rb,definition,eq(c,zero),-eq(a,zero))
            seed(ra,rb,definition,eq(c,zero),-eq(b,zero))
        seed(definition,eq(a,zero),eq(b,zero),-eq(c,zero))
        return c,k,rc,da+db+[definition]
    for s,y,a,b in gates:
        if s in sums: continue
        # Rewrite k-sum(negative bits) as sum(1-bit) only when the
        # constants agree modulo p. The bridge to the original sum is proved.
        if compounds:
            import ff_circuit_proof
            matched = ff_circuit_proof.regroup(g,s,bits,equalities,g.node,num,eq,domain,seed)
            if matched is not None:
                leaves,premises = matched
                if 2 <= len(leaves) <= MAX_SUM:
                    root,k,r,definitions = tree(leaves); sums[s]=root
                    link=eq(root,s)
                    seed(*premises,*definitions,-link)
                    seed(link,eq(root,zero),-eq(s,zero))
                    seed(link,eq(s,zero),-eq(root,zero))
                    continue
        leaves, negatives, constant = [], [], 0
        for term in g.nodes[s][1]:
            op,args,data = g.nodes[term]
            if term in bits: leaves.append(term)
            elif op == 'num': constant += data[0]
            elif op == 'ff.neg' and args[0] in bits: negatives.append(args[0])
            elif op == 'ff.mul' and len(args) == 2:
                for v,c in (args,args[::-1]):
                    if v in bits and g.nodes[c][0] == 'num' and g.nodes[c][2][0] % g.p == g.p-1:
                        negatives.append(v); break
                else: break
            else: break
        else:
            if constant % g.p != len(negatives) % g.p: continue
            for v in negatives:
                c = add(num(1),g.node('ff.neg',(v,)))
                if c not in bits:
                    bits[c]=domain(c,1); seed(bits[v],-bits[c])
                    for k in (0,1):
                        seed(eq(v,num(k)),-eq(c,num(1-k)))
                        seed(eq(c,num(k)),-eq(v,num(1-k)))
                leaves.append(c)
            if 2 <= len(leaves) <= MAX_SUM:
                root,k,r,definitions = tree(leaves); sums[s]=root
                link = eq(root,s)
                seed(*definitions,-link)
                seed(link,eq(root,zero),-eq(s,zero))
                seed(link,eq(s,zero),-eq(root,zero))
            continue
        continue


def produce(g, base, z3, start, timeout, version=3):
    import ff_boolean_proof as bp
    import ff_proof_pipeline as pp
    # Without a bounded sum, the original CNF is unchanged. New field atoms
    # occur in no clause, so the ordinary version-2 proof remains input-bound.
    if not g.cut_definitions:
        return bp.produce_integrated(g, base, z3, start, timeout)
    records, clauses = [], list(base.clauses)
    field = pp.FieldSession(z3)
    try:
        for candidate in g.range_seeds:
            literals = list(candidate)
            bp.require(time.monotonic() < start+timeout, 'range seed timeout')
            case = bp.Case(g,literals)
            output = field.query(case.normalized(),start+timeout,'native')
            if not output.startswith('(ff-certificate\n'): continue
            core,dag = bp.compact(g,literals,bp.fc.try_balance_certificate(output))
            records.append(dict(rule='field',literals=core,certificate=dag))
            clauses.append(bp.clause(-x for x in core))
    finally:
        field.close()
    proof = bp.produce_integrated(g,SimpleNamespace(clauses=clauses),z3,start,timeout)
    # The seed clauses occupied precisely these IDs during native search.
    records += proof['records']
    search = SimpleNamespace(records=records,clauses=list(base.clauses)+[None]*len(records))
    search.clauses[proof['root']] = ()
    result = bp.finish_proof(base,search,proof['root'])
    result['version']=version
    return result
