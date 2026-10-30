# VerCors audit PR 11415 @ 2a48201a59c3ac36546b1fc02b4681e38d96e745 (base c698bae880c654763b09d29b634b38562eafea11)

Scope (partial): ONE function, ONE obligation. Result: **proved** for that obligation only.

Source: src/smt/smt_quantifier.cpp at head, SHA256 090a35ff7812facfdeefe580f908cba200cfb6b39f5bdbc79391a15283407249 (1781 lines, fetched via GitHub blobs API). Function: `flatten` lambda inside `arith_scaled_polynomial`, lines ~712-728.

## Obligation 1 (proved): bounded worklist
Invariant: todo.size()+factors.size() <= 4 throughout, loop runs <= 8 iterations, no early-return path violates it, and on success (todo empty) factors <= 4.
Extract `FlattenBound.cpp` models expression nodes by arity only (arity[k] = child count of the k-th popped node, 0 for non-mul leaf), and todo/factors by their sizes; size_t modelled as int (valid since values are bounded by 4 + 64 under the precondition).

## Preconditions / non-vacuity
arity has 8 readable ints (half permission) with 0<=arity[k]<=64. Satisfied e.g. by all zeros (single leaf: returns 1, factors=1). The 64 bound is an environment assumption (get_num_args of a mul node is not bounded by the code; larger values only hit the guard returning 0, so the bound is a modelling simplification, not relied on for the invariant except to avoid int overflow).

## Gaps
Actual expr/app objects, ptr_buffer, to_app, and is_mul are abstracted by arity; mapping is manual. The real loop pushes all args of a mul node in the worklist; modelled as todo += n. Nothing about the rest of the PR is verified.

## Excluded changes
arith_coefficient, get_arith_definitions, remaining ~700 added lines in smt_quantifier.cpp (rational arithmetic, th_rewriter, macro_util, ast manager ownership), qi_params, quant_tactics, test file, fstar audit files. Not audited: out of the three-function/obligation budget; no coverage claimed. Division-by-possibly-zero in hints is documented in code as hints and not examined.

## Reproduce
mkdir d && cp FlattenBound.cpp d && cd d && /tmp/gh-aw/vercors/vercors --lang cpp --backend silicon --dev-total-timeout 60 $PWD/FlattenBound.cpp
VerCors 2.4.0, OpenJDK 17.0.21 (Temurin); bundled Silicon/Z3 from the release; no preprocessor beyond VerCors's.
