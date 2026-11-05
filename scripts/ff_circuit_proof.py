"""Bounded compound-bit recognition; matching never authorizes a proof step."""
import itertools
from functools import lru_cache
import math


def regroup(g, total, bits, equalities, node, number, equality, domain, seed):
    """Return bit summands and original wire premises, or decline this sum.

    Expand only a small local cone, then recognize Boolean polynomial identities.
    Keeping wire equalities as premises allows the final PAC bridge to recover
    their original representation, even when equations occur under disjunction.
    """
    p = g.p
    definitions = {}
    for atom in equalities:
        for var,expr in (g.nodes[atom][1],g.nodes[atom][1][::-1]):
            if g.nodes[var][0] == 'var' and var not in bits and g.nodes[expr][0] in ('ff.add','ff.mul','ff.neg'):
                definitions.setdefault(var,(expr,atom))
    used = set()
    class Decline(Exception): pass
    def add(a,b):
        result=dict(a)
        for m,c in b.items():
            c=(result.get(m,0)+c)%p
            if c: result[m]=c
            else: result.pop(m,None)
        if len(result)>64: raise Decline()
        return result
    def multiply(a,b):
        result={}
        for ma,ca in a.items():
            for mb,cb in b.items():
                m=tuple(sorted(ma+mb))
                if len(m)>2: raise Decline()
                result=add(result,{m:ca*cb%p})
        return result
    # Shared arithmetic DAGs must not be unfolded exponentially. The stack
    # remains part of the key so memoization preserves the wire-depth bound.
    @lru_cache(maxsize=512)
    def expand(i,stack=()):
        if i in bits: return {(i,):1}
        op,args,data=g.nodes[i]
        if op=='num': return {():data[0]%p} if data[0]%p else {}
        if op=='var' and i in definitions:
            if i in stack or len(stack)>=4: raise Decline()
            expr,atom=definitions[i];used.add(atom)
            return expand(expr,stack+(i,))
        if op=='ff.neg': return {m:-c%p for m,c in expand(args[0],stack).items()}
        if op in ('ff.add','ff.mul'):
            result={} if op=='ff.add' else {():1}
            for a in args: result=(add if op=='ff.add' else multiply)(result,expand(a,stack))
            return result
        raise Decline()
    try: poly=expand(total)
    except (Decline, RecursionError): return None
    leaves=[]
    def take(pattern, sign):
        nonlocal poly
        poly=add(poly,{m:-sign*c%p for m,c in pattern.items()})
    def register(pattern, inputs, sign):
        terms=[]
        for monomial,coefficient in sorted(pattern.items()):
            term=monomial[0] if len(monomial)==1 else node('ff.mul',monomial)
            if coefficient%p!=1: term=node('ff.mul',(number(coefficient),term))
            terms.append(term)
        expr=terms[0] if len(terms)==1 else node('ff.add',terms)
        if expr not in bits:
            bits[expr]=domain(expr,1)
            seed(*(bits[x] for x in inputs),-bits[expr])
            # These truth-table rows involve at most three local input bits,
            # never all circuit inputs. Each row is independently certified.
            for values in itertools.product((0,1),repeat=len(inputs)):
                assignment=dict(zip(inputs,values))
                value=sum(c*math.prod(assignment[x] for x in m) for m,c in pattern.items())%p
                if value not in (0,1): raise Decline()
                seed(*(equality(x,number(v)) for x,v in zip(inputs,values)),-equality(expr,number(value)))
        leaves.append((expr,sign));take(pattern,sign)
    try:
        # XOR: a+b-2ab is Boolean. MUX: b+s(a-b) selects b or a.
        # Signs belong to the enclosing affine sum, not to the bit domain.
        while any(len(m)==2 for m in poly):
            found=False
            for m,c in list(poly.items()):
                if len(m)!=2 or m[0]==m[1]: continue
                a,b=m
                for sign in (1,-1):
                    if c==(-2*sign)%p and poly.get((a,))==sign%p and poly.get((b,))==sign%p:
                        register({(a,):1,(b,):1,m:-2},(a,b),sign);found=True;break
                    if c!=sign%p: continue
                    for selector,yes in ((a,b),(b,a)):
                        for other,d in list(poly.items()):
                            if len(other)!=2 or selector not in other or other==m or d!=(-sign)%p: continue
                            no=other[1] if other[0]==selector else other[0]
                            if len({selector,yes,no})!=3 or poly.get((no,))!=sign%p: continue
                            register({(no,):1,m:1,other:-1},(selector,yes,no),sign);found=True;break
                        if found: break
                    if found: break
                if found: break
            if not found:
                # An uncombined product of bits is itself a bit (AND).
                m=next(m for m in poly if len(m)==2);c=poly[m]
                if c not in (1,p-1): return None
                register({m:1},tuple(sorted(set(m))),1 if c==1 else -1)
        constant=poly.pop((),0)
        for m,c in poly.items():
            if len(m)!=1 or c not in (1,p-1): return None
            leaves.append((m[0],1 if c==1 else -1))
        negative=sum(sign<0 for _,sign in leaves)
        if constant%p!=negative%p: return None
        result=[]
        for x,sign in leaves:
            if sign<0:
                expr=node('ff.add',(number(1),node('ff.neg',(x,))))
                if expr not in bits:
                    bits[expr]=domain(expr,1);seed(bits[x],-bits[expr])
                    for v in (0,1):
                        seed(equality(x,number(v)),-equality(expr,number(1-v)))
                        seed(equality(expr,number(v)),-equality(x,number(1-v)))
                x=expr
            result.append(x)
        return result,sorted(used)
    except Decline: return None
