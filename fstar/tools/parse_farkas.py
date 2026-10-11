#!/usr/bin/env python3
"""
parse_farkas.py

A small preprocessing parser that reads a real Z3 proof-output file
(produced by `z3.exe smt.arith.solver=2 <file>.smt2` on a `.smt2` file
containing `(set-option :produce-proofs true)` plus a `(get-proof)`
after `(check-sat)`), locates the `(_ th-lemma arith farkas c1 .. cn)`
proof node, resolves each antecedent back to its raw arithmetic
literal (following the `let`-bound alias chain Z3's own proof printer
emits), and emits a ready-to-typecheck `cert_entry` list literal in
Z3LraFarkasTheory.fst's F* syntax -- i.e. this is the "parser" that
turns a genuine Z3 proof artifact into the structured input
`farkas_decide`/`check_farkas_decide` consume, so the Pulse checker is
exercised on parsed real proof data, not only hand-transcribed
certificates.

This is *not* part of the trusted F*/Pulse formalization itself (it is
an ordinary Python preprocessing script, the same role a build-time
code generator would play); everything it emits is independently
re-verified by F*'s own type checker exactly like any other `.fst`
literal -- a bug in this script could only ever produce a certificate
F* then *correctly rejects* (`farkas_decide ... == None`), not a false
positive, since `farkas_decide`'s own soundness proof
(`lemma_farkas_decide_sound`) does not depend on anything this script
does.

Usage:
    python parse_farkas.py <proof-output-file> [<proof-output-file> ...]

Scope (documented limitation, see LRA_FARKAS_REPORT.md):
  - only handles the common "single `false` conclusion, every
    antecedent asserted positively (`is_pos = true`)" shape, which is
    what every real certificate harvested for this project uses (see
    `Z3LraFarkasTheory.fst`'s module header); an antecedent fed in
    already negated, or a disjunctive conclusion with per-disjunct
    coefficients, is out of scope and will raise `NotImplementedError`.
  - only linear (`+`/`-`/`*`-by-constant/`/`-by-constant) arithmetic
    expressions are evaluated; encountering a nonlinear sub-term
    raises `ValueError`.
"""
import re
import sys
from fractions import Fraction


# --------------------------------------------------------------------
# A minimal S-expression tokenizer/parser.
# --------------------------------------------------------------------

def tokenize(text):
    return re.findall(r"\(|\)|[^\s()]+", text)


def parse_sexprs(tokens):
    pos = [0]

    def parse_one():
        tok = tokens[pos[0]]
        if tok == "(":
            pos[0] += 1
            items = []
            while tokens[pos[0]] != ")":
                items.append(parse_one())
            pos[0] += 1
            return items
        else:
            pos[0] += 1
            return tok

    forms = []
    while pos[0] < len(tokens):
        forms.append(parse_one())
    return forms


# --------------------------------------------------------------------
# Collect every `(let ((name val)) body)` binding anywhere in the tree
# into one flat dict (names are unique in Z3's own proof printer
# output, so this is safe even though the dict ignores scoping).
# --------------------------------------------------------------------

def collect_defs(sexpr, defs):
    if isinstance(sexpr, list):
        if sexpr and sexpr[0] == "let" and len(sexpr) >= 2:
            bindings = sexpr[1]
            for b in bindings:
                name, val = b[0], b[1]
                defs[name] = val
        for sub in sexpr:
            collect_defs(sub, defs)


def find_th_lemma_farkas(sexpr):
    """Depth-first search for the `((_ th-lemma arith farkas c1 .. cn) ...)`
       application node; returns (coeffs, antecedent-terms, conclusion)."""
    if isinstance(sexpr, list):
        if (sexpr and isinstance(sexpr[0], list) and len(sexpr[0]) >= 4
                and sexpr[0][0] == "_" and sexpr[0][1] == "th-lemma"
                and sexpr[0][2] == "arith" and sexpr[0][3] == "farkas"):
            coeffs = [Fraction(c) for c in sexpr[0][4:]]
            args = sexpr[1:]
            return coeffs, args[:-1], args[-1]
        for sub in sexpr:
            r = find_th_lemma_farkas(sub)
            if r is not None:
                return r
    return None


def resolve_fact(term, defs):
    """An antecedent proof-term's final justified fact: repeatedly
       unwrap one "proof application -> its last argument" step (for
       `asserted`/`mp`/`and-elim`/...), and one `let`-alias step for
       bare symbols, until a literal relation expression (`<=`/`<`/
       `>=`/`>`/`=`) is reached."""
    cur = term
    for _ in range(200):
        if isinstance(cur, list):
            if cur and cur[0] in REL_OPS:
                return cur
            if not cur:
                return cur
            cur = cur[-1]
        elif isinstance(cur, str):
            if cur in defs:
                cur = defs[cur]
            else:
                return cur
        else:
            return cur
    raise ValueError("resolve_fact: too many resolution steps for " + str(term))


# --------------------------------------------------------------------
# Linear-arithmetic evaluator: sexpr -> (dict[var, Fraction], Fraction)
# --------------------------------------------------------------------

_num_re = re.compile(r"^-?\d+(\.\d+)?$")


def is_number(tok):
    return isinstance(tok, str) and _num_re.match(tok) is not None


def add_terms(t1, t2, sign=1):
    coeffs = dict(t1[0])
    for v, c in t2[0].items():
        coeffs[v] = coeffs.get(v, Fraction(0)) + sign * c
    return coeffs, t1[1] + sign * t2[1]


def scale_term(t, k):
    return {v: c * k for v, c in t[0].items()}, t[1] * k


def eval_lin(sexpr, defs):
    if isinstance(sexpr, str):
        if is_number(sexpr):
            return {}, Fraction(sexpr)
        if sexpr in defs:
            return eval_lin(defs[sexpr], defs)
        return {sexpr: Fraction(1)}, Fraction(0)
    op = sexpr[0]
    args = sexpr[1:]
    if op == "+":
        acc = ({}, Fraction(0))
        for a in args:
            acc = add_terms(acc, eval_lin(a, defs))
        return acc
    if op == "-":
        if len(args) == 1:
            return scale_term(eval_lin(args[0], defs), Fraction(-1))
        acc = eval_lin(args[0], defs)
        for a in args[1:]:
            acc = add_terms(acc, eval_lin(a, defs), sign=-1)
        return acc
    if op == "*":
        evaled = [eval_lin(a, defs) for a in args]
        nonconst = [e for e in evaled if e[0]]
        if len(nonconst) > 1:
            raise ValueError("nonlinear term: " + str(sexpr))
        k = Fraction(1)
        for e in evaled:
            if not e[0]:
                k *= e[1]
        if nonconst:
            return scale_term(nonconst[0], k)
        return {}, k
    if op == "/":
        num = eval_lin(args[0], defs)
        den = eval_lin(args[1], defs)
        if den[0]:
            raise ValueError("nonlinear denominator: " + str(sexpr))
        return scale_term(num, Fraction(1) / den[1])
    raise ValueError("unsupported operator in linear term: " + op)


REL_OPS = {"<=": "Le", "<": "Lt", ">=": "Ge", ">": "Gt", "=": "Eqr"}


def parse_literal(sexpr, defs):
    """`(<rel> a0 a1)` -> (rel-name, (coeffs0, cst0), (coeffs1, cst1))."""
    if not (isinstance(sexpr, list) and len(sexpr) == 3 and sexpr[0] in REL_OPS):
        raise NotImplementedError("unsupported antecedent literal shape: " + str(sexpr))
    rel = REL_OPS[sexpr[0]]
    return rel, eval_lin(sexpr[1], defs), eval_lin(sexpr[2], defs)


def normalize_pos(rel, t0, t1):
    """`normalize true l` from Z3LraFarkasTheory.fst: returns
       (term:(coeffs,cst), strict:bool, is_eq:bool)."""
    if rel == "Eqr":
        return add_terms(t0, t1, sign=-1), False, True
    if rel == "Le":
        return add_terms(t0, t1, sign=-1), False, False
    if rel == "Lt":
        return add_terms(t0, t1, sign=-1), True, False
    if rel == "Ge":
        return add_terms(t1, t0, sign=-1), False, False
    if rel == "Gt":
        return add_terms(t1, t0, sign=-1), True, False
    raise ValueError(rel)


def lcm(a, b):
    from math import gcd
    return a * b // gcd(a, b)


def denominators_of(term):
    coeffs, cst = term
    ds = [c.denominator for c in coeffs.values()] + [cst.denominator]
    return ds


def scale_int(term, k):
    coeffs, cst = term
    new_coeffs = {}
    for v, c in coeffs.items():
        scaled = c * k
        assert scaled.denominator == 1, (v, c, k)
        new_coeffs[v] = scaled.numerator
    scaled_cst = cst * k
    assert scaled_cst.denominator == 1
    return new_coeffs, scaled_cst.numerator


def parse_farkas_certificate(text):
    tokens = tokenize(text)
    forms = parse_sexprs(tokens)
    defs = {}
    for f in forms:
        collect_defs(f, defs)
    found = None
    for f in forms:
        found = find_th_lemma_farkas(f)
        if found is not None:
            break
    if found is None:
        raise ValueError("no `th-lemma arith farkas` node found")
    coeffs, antecedents, conclusion = found
    if conclusion != "false":
        raise NotImplementedError("only single-`false`-conclusion certificates are supported")
    entries = []
    denom_scales = []
    parsed_atoms = []
    for c, ant in zip(coeffs, antecedents):
        fact = resolve_fact(ant, defs)
        rel, t0, t1 = parse_literal(fact, defs)
        term, strict, is_eq = normalize_pos(rel, t0, t1)
        d = 1
        for dd in denominators_of(term):
            d = lcm(d, dd)
        parsed_atoms.append((term, strict, is_eq, c, d))
        denom_scales.append(d)
    overall_d = 1
    for d in denom_scales:
        overall_d = lcm(overall_d, d)
    for term, strict, is_eq, c, d in parsed_atoms:
        scaled_term = scale_int(term, d)
        scaled_coeff = c * overall_d / d
        assert scaled_coeff.denominator == 1
        entries.append((scaled_term, strict, is_eq, scaled_coeff.numerator))
    return entries


# --------------------------------------------------------------------
# F* code generation.
# --------------------------------------------------------------------

def fstar_lin_term(term):
    coeffs, cst = term
    mono = "; ".join('(%d, "%s")' % (v_c, v) for v, v_c in coeffs.items())
    return "{ mono = [%s]; cst = %d }" % (mono, cst)


def fstar_cert(name, entries):
    lines = ["let %s : list cert_entry =" % name, "  ["]
    rows = []
    for term, strict, is_eq, c in entries:
        rows.append('    { a = { term = %s; strict = %s; is_eq = %s }; c = %d }'
                     % (fstar_lin_term(term), str(strict).lower(), str(is_eq).lower(), c))
    lines.append(";\n".join(rows))
    lines.append("  ]")
    return "\n".join(lines)


if __name__ == "__main__":
    for path in sys.argv[1:]:
        with open(path) as f:
            text = f.read()
        entries = parse_farkas_certificate(text)
        name = re.sub(r"[^a-zA-Z0-9_]", "_", path.rsplit("/", 1)[-1].rsplit("\\", 1)[-1].rsplit(".", 1)[0])
        print("(* parsed from %s *)" % path)
        print(fstar_cert("parsed_" + name + "_cert", entries))
        print()
