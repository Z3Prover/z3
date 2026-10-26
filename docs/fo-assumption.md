# Open predicate assumptions

## Goal and API

Extend `Solver.check(*assumptions)` / `Z3_solver_check_assumptions` with open
predicate templates. For example:

```python
p = Function("p", IntSort(), IntSort(), BoolSort())
result = solver.check(p(Var(1, IntSort()), Var(0, IntSort())))
```

The accepted open form is a positive application of an uninterpreted Boolean
predicate of arity `n > 0` to exactly `Var(n-1), ..., Var(0)`, with each
variable's sort matching the corresponding argument sort. These are free
de Bruijn variables, not constants and not an explicitly quantified formula.
Negated templates, repeated/permuted variables, partial applications, and other
formulas containing free variables are rejected. Closed assumptions retain their
existing behavior, including closed quantified formulas.

The native SMT context supports the feature. `SimpleSolver()` selects it
directly; the ordinary `Solver()` uses its incremental SMT backend when given
assumptions. Other solver implementations opt in explicitly or report an error.
In particular, a tactic-created solver is not a substitute for `SimpleSolver()`.
Multi-threaded SMT and its optional SLS model shortcut are not supported for open
assumptions.

## Semantics

During this check, every internalized ground Boolean application whose declaration
is the template's predicate is assumed true, regardless of relevance or argument
values. This includes atoms already internalized by earlier operations and atoms
introduced by quantifier instantiation or theory reasoning during search.
Different declarations with the same printed name are not confused.

This is an internalization-driven assumption schema, not eager enumeration of a
domain and not a replacement for asserting `ForAll(..., p(...))`. Terms removed
by preprocessing or never internalized do not create assumptions. An unused open
predicate is vacuous; it does not force the predicate's interpretation everywhere
in a returned model.

Assumptions are local to a check. A later check without the template does not
force these instances. User push/pop scopes continue to govern assertions as
before. Once discovered, an instance is retained for the remainder of this check,
including backtracking and theory-requested research.

## SMT implementation

The solver boundary recognizes and validates open templates before dispatch.
Unsupported backends reject them rather than interpreting free variables as
ordinary Boolean assumptions. The SMT context also validates inputs for callers
that bypass the public solver wrapper.

The context records the selected predicate declarations, scans existing Boolean
variables, and observes newly allocated Boolean variables. Matching ground atoms
are reference-counted and deduplicated for the check. The template itself is never
asserted or internalized as an ordinary formula.

Following the additional implementation suggestion below, the context creates a
fresh, private dummy literal at the assumption level and asserts guarded instances:

```text
decision level 1: dummy
                 dummy => p(t1, t2)
                 dummy => p(u1, u2)
```

Level 1 here means the internal assumption scope above the current user/base
scope, not an extra user `push`. Ordinary assumptions share that scope.

Internalization callbacks only enqueue atoms: backtracking while an internalizer
or theory callback is on the stack is unsafe. At a safe search boundary, the
context returns to the assumption level, re-internalizes queued atoms there, and
adds their guarded clauses. It does not proceed to decisions or report a model
while unprocessed instances remain. Ground terms are retained by AST references
even if their higher-level Boolean variables are deleted by this promotion.
This initial implementation favors a clear lifetime invariant over avoiding
backtracking on each batch of late instances.

The guard, instance clauses, and assumption flags use the existing temporary
assumption scope and are removed with it. Predicate watching is scoped to the
check, including exception unwinding. No open-assumption state is copied into a
different solver or an unsupported parallel search.

## Core extraction and proofs

Each activated ground atom is marked as an assumption and mapped to its own AST,
not to the open template. Conflict resolution stops at positively assigned open
atoms when traversing their reasons, instead of following their guarded
justifications to the dummy. The private dummy is excluded from the exported core.

For a negatively assigned atom, core traversal must still follow the reason for
that negative assignment: it can depend on closed assumptions that must also
appear in the core. Cutting traversal at a negative occurrence would be unsound.

Consequently a core can contain several applications of one open predicate:

```text
input assumption: p(Var(1), Var(0))
assertion:        not p(a, b) or not p(b, a)
core:             [p(a, b), p(b, a)]
```

Such a core is not literally a subset of the input templates. Rechecking the
original assertions with the returned ground core as ordinary closed assumptions
must be unsatisfiable. Existing core validation and minimization operate on these
closed instances. As with ordinary cores, the result need not be minimal and does
not enumerate every possible answer.

Proof construction continues to use asserted proofs for the temporary dummy and
guarded clauses. These internal premises can occur in the proof even though the
public core presents ground instances.

## Python examples and tests

Run `examples\python\open_assumptions.py` against the checkout's built Python
bindings. It demonstrates both a binary predicate with a two-instance core and
first-order answer extraction.

For example, from the repository root in PowerShell, after building the
`build_z3_python_bindings` target:

```powershell
$env:PYTHONPATH = "$PWD\build\python"
$env:Z3_LIBRARY_PATH = "$PWD\build"
python examples\python\open_assumptions.py
python -m unittest discover -s examples\python -p test_open_assumptions.py -v
```

Set both paths to avoid mixing the checkout's bindings with an older native
library elsewhere on `PATH`.

For answer extraction, instrument an implication with a negative answer literal:

```python
researcher = Function("researcher", Person, BoolSort())
reject = Function("reject-answer", Person, BoolSort())
s.add(researcher(alice), researcher(bob))
s.add(ForAll([x], Implies(researcher(x), Not(reject(x))),
             patterns=[researcher(x)]))
assert s.check(reject(Var(0, Person))) == unsat
answers = [literal.arg(0) for literal in s.unsat_core()]
```

An instance such as `reject(alice)` in the core identifies an answer established
by the background theory. The open template lets the solver discover the ground
answer term; the caller need not know or supply it in advance. This sign convention
uses positive open assumptions to contradict negative answer literals.

Focused regressions live in `src\test\check_assumptions.cpp` and
`examples\python\test_open_assumptions.py`. They check actual returned cores by
re-solving under their ground instances, as well as incremental cleanup, mixed
closed/open assumptions, late instantiation, malformed input, and backend errors.

## Creation instructions

The original request is reproduced verbatim:

```text
pull
create a branch call fo-assumption
checkout fo-assumption
create a design documet under docs called fo-assumption.md
The desig document describes how to augment z3's assumption literals with open predicates.
An open predicate is of the form (p (:var 1) (:var 0)), for the example of binary predicates, where :var 1, :var 0 are de-Brujin variables and p is a binary predicate.
The task is to make sure that the API accepts open assumptions of this form.
Then it processes open assumptions differently from close assumptions: Whenever a ground term (p t1 t2) is internalized, the ground term with p as the function symbol is added as an assumption (forced true within decision level 1 of search).
A core with open assumptions can therefore have multiple uses of p, none of them are ground in the input.
Make sure that the smt_context solver works with open assumptions.
Other cores that on't work yet with open assumptions can throw exceptions.
Add some examples using the Python API for use cases of open assumptions.
For example, consider cases from first-order answer literals.
You want to include this prompt in fo-assumption.md as documentaiton for how it was created.
```

Additional instructions, in order:

```text
make sure to update with current master.
push the branch
```

The scope clarification selected:

```text
Design document, implementation, and runnable Python examples.
```

The subsequent implementation and documentation instructions were:

```text
you can use a dummy assumption literal at level 1, and assert dummy => (p t1 t2). Have conflict resolution stop at (p t1 t2) instead of dummy when producing the core.
```

```text
include extra instructions in the markdown file for documetaiton
```
