# Real-World ERE Equivalence Benchmarks

Pairwise regex equivalence checks across 7 practical categories.
Each .smt2 file asks: *do these two regexes accept exactly the same strings?*

## Format

```smt2
(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x (R1⊕R2)))   ;; symmetric difference
(check-sat)
```

- **unsat** → regexes are equivalent
- **sat** → regexes differ (x is a distinguishing witness)

## Categories

| Category | Regexes | Pairs | Description |
|----------|---------|-------|-------------|
| url | 8 | 28 | URL validation |
| email | 6 | 15 | Email validation |
| ipv4 | 5 | 10 | IPv4 addresses |
| date | 5 | 10 | Date formats |
| phone | 5 | 10 | Phone numbers |
| css | 6 | 15 | CSS colors |
| snort | 5 | 10 | Snort/DPI patterns |
| **Total** | **40** | **98** | |

## Running

```bash
# Z3
z3 -T:60 realworld/url/url_000_*.smt2

# resharp-solver (CAV25)
resharp-solver realworld/url/url_000_*.smt2

# Full benchmark suite
node run_realworld.js
```

## Motivation

These benchmarks model a practical engineering question:
*"Do these two regexes, written for the same validation task, accept the same strings?"*

Inspired by the Mathias Bynens URL regex comparison (mathiasbynens.be/demo/url-regex)
which shows 13 different URL validation regexes that disagree on 72 test URLs.

## ERE Features Exercised

- Large character classes (ASCII printable = 95 chars)
- Bounded repetition (`re.loop`)
- Intersection and complement (`re.inter`, `re.comp`)
- Complex alternation structures
- Nested concatenation with optional parts
