#!/usr/bin/env python3
"""
parse_rewrite_tags.py

Extracts every rule-tagged `PR_REWRITE` leaf -- printed by Z3 as
`((_ rewrite <tag>) (= lhs rhs))` (or `(~ lhs rhs)` for the oeq-flavored
variant) -- out of a real Z3 `(get-proof)` text dump, where `<tag>` is the
`family:decl-name` symbol parameter now attached by
`th_rewriter_cfg::tag_rewrite` (src/ast/rewriter/th_rewriter.cpp).

This is a genuine S-expression scan (tokenizer + recursive-descent parser),
not a regex/string hack: proof terms are deeply nested and the same
sub-term can appear inside `let`-bindings, `monotonicity`/`trans` wrapping,
etc., so a reliable extractor has to walk the actual parsed tree looking
for applications whose head is the two-element list `(_ rewrite <tag>)`.

Usage:
    python parse_rewrite_tags.py <file1.txt> [<file2.txt> ...]

Prints, for each file, every (tag, lhs, rhs) triple found, deduplicated.
"""
import sys


def tokenize(text):
    tokens = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n":
            i += 1
        elif c in "()":
            tokens.append(c)
            i += 1
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 1
            tokens.append(text[i:j + 1])
            i = j + 1
        else:
            j = i
            while j < n and text[j] not in " \t\r\n()":
                j += 1
            tokens.append(text[i:j])
            i = j
    return tokens


def parse_all(tokens):
    """Parse a token stream into a list of top-level S-expressions."""
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

    exprs = []
    while pos[0] < len(tokens):
        exprs.append(parse_one())
    return exprs


def to_str(sexpr):
    if isinstance(sexpr, list):
        return "(" + " ".join(to_str(x) for x in sexpr) + ")"
    return sexpr


def is_tagged_rewrite_head(x):
    """True if x is the S-expr `(_ rewrite <tag>)`."""
    return (isinstance(x, list) and len(x) == 3
            and x[0] == "_" and x[1] == "rewrite")


def collect_let_defs(sexpr, defs):
    """Z3 prints shared sub-proofs/sub-terms once via `(let ((name val) ...)
    body)`. The tagged rewrite's single argument is frequently just such a
    `name` rather than an inline `(= lhs rhs)`, so build a flat name->value
    table (across the whole proof, like a global symbol table) that lets us
    resolve any alias back to its defining expression."""
    if not isinstance(sexpr, list):
        return
    if len(sexpr) == 3 and sexpr[0] == "let" and isinstance(sexpr[1], list):
        for binding in sexpr[1]:
            if isinstance(binding, list) and len(binding) == 2:
                name, val = binding
                defs[name] = val
    for child in sexpr:
        collect_let_defs(child, defs)


def resolve_fact(x, defs, limit=50):
    """Repeatedly peel `symbol -> its let-definition` until reaching a
    literal `(= a b)`/`(~ a b)` relation expression, or giving up."""
    for _ in range(limit):
        if isinstance(x, list) and len(x) == 3 and x[0] in ("=", "~"):
            return x
        if isinstance(x, str) and x in defs:
            x = defs[x]
            continue
        return None
    return None


def resolve_term(x, defs, limit=50):
    """Recursively resolve any `let`-bound alias symbol appearing anywhere
    inside a term (not just at the top level), matching the same
    alias-resolution need `tools/parse_farkas.py` documented for linear
    arithmetic sub-expressions."""
    seen = set()
    while isinstance(x, str) and x in defs and x not in seen:
        seen.add(x)
        x = defs[x]
    if isinstance(x, list):
        return [resolve_term(c, defs, limit) for c in x]
    return x


def find_tagged_rewrites(sexpr, defs, out):
    """Recursively scan `sexpr`, collecting (tag, lhs, rhs) for every
    application `((_ rewrite <tag>) <fact>)` where `<fact>` resolves
    (directly, or via `defs`) to `(= lhs rhs)`/`(~ lhs rhs)`."""
    if not isinstance(sexpr, list):
        return
    if len(sexpr) == 2 and is_tagged_rewrite_head(sexpr[0]):
        fact = resolve_fact(sexpr[1], defs)
        if fact is not None:
            tag = sexpr[0][2]
            lhs = resolve_term(fact[1], defs)
            rhs = resolve_term(fact[2], defs)
            out.append((tag, to_str(lhs), to_str(rhs)))
    for child in sexpr:
        find_tagged_rewrites(child, defs, out)


def main():
    for path in sys.argv[1:]:
        with open(path, encoding="utf-8") as f:
            text = f.read()
        tokens = tokenize(text)
        exprs = parse_all(tokens)
        found = []
        for e in exprs:
            defs = {}
            collect_let_defs(e, defs)
            find_tagged_rewrites(e, defs, found)
        # de-duplicate while preserving first-seen order
        seen = set()
        uniq = []
        for triple in found:
            if triple not in seen:
                seen.add(triple)
                uniq.append(triple)
        print(f"=== {path} ===")
        if not uniq:
            print("  (no tagged rewrites found)")
        for tag, lhs, rhs in uniq:
            print(f"  [{tag}]  {lhs}  =  {rhs}")
        print()


if __name__ == "__main__":
    main()
