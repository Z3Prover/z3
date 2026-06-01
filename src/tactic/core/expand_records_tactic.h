/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    expand_records_tactic.h

Author:

    Lev Nachmanson 2026-05

Tactic Documentation:

## Tactic expand-records

### Short Description

Replace every free constant of a single-constructor algebraic datatype
sort with the corresponding constructor applied to fresh field
variables.  For example, `(declare-fun p () Pair)` with the single
constructor `mk-pair(first:Int, second:Int)` is replaced by the
substitution `p -> (mk-pair p!first p!second)` for fresh `p!first` and
`p!second`.

After the rewrite, accessor applications `(first p)`, `(second p)`
collapse to the corresponding field variables, allowing subsequent
solve-eqs and arithmetic simplification to make better use of constant
folding.

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/expand_records.h"

inline tactic * mk_expand_records_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& mm, auto& pp, auto &ss) -> dependent_expr_simplifier* {
                     return alloc(expand_records_simplifier, mm, pp, ss);
                 });
}

/*
  ADD_TACTIC("expand-records", "expand single-constructor datatype constants.", "mk_expand_records_tactic(m, p)")
*/
