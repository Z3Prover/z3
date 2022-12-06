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

Example, suppose we have a function `f` with `2` arguments. 
There are 1000 applications of this function, but the first argument is always "a", "b" or "c".
Thus, we replace the `f(t1, t2)` with 

*      `f_a(t2)`   if   `t1 = a`
*      `f_b(t2)`   if   `t2 = b`
*      `f_c(t2)`   if   `t2 = c`

Since `f_a`, `f_b`, `f_c` are new symbols, satisfiability is preserved.
   
This transformation is very similar in spirit to the Ackermman's reduction. 

This transformation should work in the following way:

```
   1- Create a mapping decl2arg_map from declarations to tuples of booleans, an entry [f -> (true, false, true)]
       means that f is a declaration with 3 arguments where the first and third arguments are always values.
   2- Traverse the formula and populate the mapping. 
        For each function application f(t1, ..., tn) do
          a) Create a boolean tuple (is_value(t1), ..., is_value(tn)) and do
             the logical-and with the tuple that is already in the mapping. If there is no such tuple
             in the mapping, we just add a new entry.

   If all entries are false-tuples, then there is nothing to be done. The transformation is not applicable.

   Now, we create a mapping decl2new_decl from (decl, val_1, ..., val_n) to decls. Note that, n may be different for each entry,
   but it is the same for the same declaration.
   For example, suppose we have [f -> (true, false, true)] in decl2arg_map, 
  and applications f(1, a, 2), f(1, b, 2), f(1, b, 3), f(2, b, 3), f(2, c, 3) in the formula.
   Then, decl2arg_map would contain
        (f, 1, 2) -> f_1_2
        (f, 1, 3) -> f_1_3
        (f, 2, 3) -> f_2_3
   where f_1_2, f_1_3 and f_2_3 are new function symbols.
   Using the new map, we can replace the occurrences of f.
```

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
class ast_manager;
class tactic;

tactic * mk_reduce_args_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("reduce-args", "reduce the number of arguments of function applications, when for all occurrences of a function f the i-th is a value.", "mk_reduce_args_tactic(m, p)")
*/

