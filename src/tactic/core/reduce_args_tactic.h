/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    reduce_args_tactic.h

Abstract:

    Reduce the number of arguments in function applications.

Author:

    Leonardo (leonardo) 2012-02-19

Tactic Documentation:

## Tactic reduce-args

### Short Description:

Reduce the number of arguments of function applications, when for all occurrences of a function f the i-th is a value.

### Long Description

Example, suppose we have a function $f$ with 2 arguments. 
There are 1000 applications of this function, but the first argument is always $a$, $b$ or $c$.
Thus, we replace the $f(t_1, t_2)$ with 

* $f_a(t_2)$   if   $t_1 = a$
* $f_b(t_2)$   if   $t_2 = b$
* $f_c(t_2)$   if   $t_2 = c$

Since $f_a$, $f_b$, $f_c$ are new symbols, satisfiability is preserved.
   
This transformation is very similar in spirit to the Ackermman's reduction. 
For each function `f` and argument position of `f` it checks if all occurrences of `f` uses a value at position `i`.
The values may be different, but all occurrences have to be values for the reduction to be applicable. 
It creates a fresh function for each of the different values at position `i`.


### Example
 
```z3
(declare-fun f (Int Int) Bool)
(declare-const x Int)
(assert (f 1 2))
(assert (f 1 3))
(assert (f 2 4))
(assert (f 2 5))
(assert (f 1 6))
(assert (f 1 7))
(assert (f 1 x))
(apply reduce-args)
```

### Notes

* supports unsat cores
* does not support proof terms

--*/
#pragma once

#include "util/params.h"
#include "ast/simplifiers/reduce_args_simplifier.h"
#include "tactic/dependent_expr_state_tactic.h"
class ast_manager;
class tactic;

tactic * mk_reduce_args_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("reduce-args", "reduce the number of arguments of function applications, when for all occurrences of a function f the i-th is a value.", "mk_reduce_args_tactic(m, p)")
*/

inline tactic* mk_reduce_args_tactic2(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p, 
        [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* { return mk_reduce_args_simplifier(m, s, p); });
}
/*
  ADD_TACTIC("reduce-args2", "reduce the number of arguments of function applications, when for all occurrences of a function f the i-th is a value.", "mk_reduce_args_tactic2(m, p)")
  ADD_SIMPLIFIER("reduce-args", "reduce the number of arguments of function applications, when for all occurrences of a function f the i-th is a value.", "mk_reduce_args_simplifier(m, s, p)")

*/

