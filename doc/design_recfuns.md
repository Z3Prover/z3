# Design for handling recursive functions

Main source of inspiration is [Sutter, Köksal & Kuncak 2011],
as implemented in Leon, but the main
differences is that we should unroll function definitions directly from the
inside of Z3, in a backtracking way. Termination and fairness are ensured by
iterative-deepening on the maximum number of unrollings in a given branch.

## Unfolding

The idea is that every function definition `f(x1…xn) := rhs[x1…xn]` is
compiled into:

- a list of cases `A_f_i[x1…xn] => f(x1…xn) = rhs_i[x1…xn]`.
  When `A_f_i[t1…tn]` becomes true in the model, `f(t1…tn)` is said to be
  *unfolded* and the clause `A_f_i[t1…tn] => f(t1…tn) = rhs_i[t1…tn]`
  is added as an auxiliary clause.
- a list of constraints `Γ_f_i[x1…xn] <=> A_f_i[x1…xn]`
  that states when `A_f_i[x1…xn]` should be true, depending on inputs `x1…xn`.
  For every term `f(t1…tn)` present in congruence closure, we
  immediately add all the `Γ_f_i[t1…tn] <=> A_f_i[t1…tn]` as auxiliary clauses
  (maybe during internalization of `f(t1…tn)`?).

where each `A_f_i[x1…xn]` is a special new predicate representing the
given case of `f`, and `rhs_i` does not contain any `ite`.
We assume pattern matching has been compiled to `ite` beforehand.

For example, `fact(n) := if n<2 then 1 else n * fact(n-1)` is compiled into:

- `A_fact_0[n] => fact(n) = 1`
- `A_fact_1[n] => fact(n) = n * fact(n-1)`
- `A_fact_0[n] <=> n < 2`
- `A_fact_1[n] <=> ¬(n < 2)`

The 2 first clauses are only added when `A_fact_0[t]` is true
(respectively `A_fact_1[t]` is true).
The 2 other clauses are added as soon as `fact(t)` is internalized.

## Termination

To ensure termination, we define variables:

- `unfold_depth: int`
- `current_max_unfold_depth: int`
- `global_max_unfold_depth: int`

and a special literal `[max_depth=$n]` for each `n:int`.
Solving is done under the local assumption
`[max_depth=$current_max_unfold_depth]` (this should be handled in some outer
loop, e.g. in a custom tactic).

Whenever `A_f_i[t1…tn]` becomes true (for any `f`), we increment
`unfold_depth`. If `unfold_depth > current_max_unfold_depth`, then
the conflict clause `[max_depth=$current_max_unfold_depth] => Γ => false`
where `Γ` is the conjunction of all `A_f_i[t1…tn]` true in the trail.

For non-recursive functions, we don't have to increment `unfold_depth`. Some other functions that are known

If the solver answers "SAT", we have a model.
Otherwise, if `[max_depth=$current_max_unfold_depth]` is part of the
unsat-core, then we increase `current_max_unfold_depth`.
If `current_max_unfold_depth == global_max_unfold_depth` then
we report "UNKNOWN" (reached global depth limit), otherwise we can
try to `solve()` again with the new assumption (higher depth limit).

## Tactic

there should be a parametrized tactic `funrec(t, n)` where `t` is the tactic
used to solve (under assumption that depth is limited to `current_max_unfold_depth`)
and `n` is an integer that is assigned to `global_max_unfold_depth`.

This way, to try and find models for a problem with recursive functions + LIA,
one could use something like `(funrec (then simplify dl smt) 100)`.

## Expected benefits

This addition to Z3 would bring many benefits compared to current alternatives (Leon, quantifiers, …)

- should be very fast and lightweight
  (compared to Leon or quantifiers).
  In particular, every function call is very lightweight even compared to Leon (no need for full model building, followed by unsat core extraction)
- possibility of answering "SAT" for any `QF_*` fragment +
  recursive functions
- makes `define-funs-rec` a first-class citizen of the language,  usable to model user-defined theories or to analyze functional
  programs directly

## Optimizations

- maybe `C_f_i` literals should never be decided on
  (they can always be propagated).
  Even stronger: they should not be part of conflicts?
  (i.e. tune conflict resolution to always resolve
   these literals away, disregarding their level)
