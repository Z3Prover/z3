/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    distinct_theory_checker.cpp

Abstract:

    Plugin for checking distinct internalization

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-07

--*/

#include "ast/ast_pp.h"
#include "sat/smt/distinct_theory_checker.h"

namespace distinct {

    expr_ref_vector theory_checker::clause(app* jst) {
        expr_ref_vector result(m);
        result.append(jst->get_num_args(), jst->get_args());
        return result;
    }

    // euf::solver::axiomatize_basic internalizes a distinct d below the root
    // with some_eq, the disjunction of the equalities of its argument pairs,
    // and the two clauses
    //     (or (not d) (not some_eq))      (or d some_eq)
    // each logged with an alldiff hint listing the clause. A distinct at the
    // root is clausified into input clauses instead, so these are the only
    // alldiff hints: a hint of any other shape is rejected.
    bool theory_checker::check(app* jst) {
        if (jst->get_num_args() != 2)
            return false;
        expr* d = jst->get_arg(0);
        expr* some_eq = jst->get_arg(1);
        bool negated = m.is_not(d, d);
        if (negated != m.is_not(some_eq, some_eq))
            return false;
        if (!m.is_distinct(d))
            std::swap(d, some_eq);
        if (!m.is_distinct(d))
            return false;
        return gate_holds(to_app(d), some_eq, negated);
    }

    // some_eq is the disjunction Z3 builds, a single equality when d has two
    // arguments, or false when it has fewer.
    bool theory_checker::gate_holds(app* d, expr* some_eq, bool negated) {
        ptr_buffer<expr> disjuncts;
        if (m.is_or(some_eq))
            disjuncts.append(to_app(some_eq)->get_num_args(), to_app(some_eq)->get_args());
        else if (!m.is_false(some_eq))
            disjuncts.push_back(some_eq);

        unsigned n = d->get_num_args();
        bool repeated = false;
        obj_hashtable<expr> arguments;
        for (expr* arg : *d) {
            if (arguments.contains(arg))
                repeated = true;
            arguments.insert(arg);
        }

        if (negated) {
            // (or (not d) (not some_eq)): every disjunct of some_eq makes d
            // false. An equality between arguments at two positions does; a
            // disjunct that holds regardless (true, or x = x for an argument
            // that occurs once) only if d is false anyway.
            for (expr* e : disjuncts) {
                expr* x, * y;
                if (m.is_false(e))
                    continue;
                if (m.is_true(e))
                    return repeated;
                if (!m.is_eq(e, x, y) || !arguments.contains(x) || !arguments.contains(y))
                    return false;
                if (x == y && !repeated)
                    return false;
            }
            return true;
        }

        // (or d some_eq): whenever d is false some pair of arguments is
        // equal, so every pair that can be equal needs its equality among
        // the disjuncts. Extra disjuncts only weaken the clause's demand.
        obj_pair_set<expr, expr> equalities;
        for (expr* e : disjuncts) {
            expr* x, * y;
            if (m.is_true(e))
                return true;
            if (m.is_eq(e, x, y))
                equalities.insert(x, y);
        }
        for (unsigned i = 0; i < n; ++i) {
            for (unsigned j = i + 1; j < n; ++j) {
                expr* x = d->get_arg(i);
                expr* y = d->get_arg(j);
                if (m.are_distinct(x, y))
                    continue;
                if (!equalities.contains(x, y) && !equalities.contains(y, x))
                    return false;
            }
        }
        return true;
    }
}
