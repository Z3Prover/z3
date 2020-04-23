/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    factor_equivs.cpp

Abstract:
  Factor equivalence classes out of an expression.

  "Equivalence class structure" for objs. Uses a union_find structure internally.
  Operations are :
  -Declare a new equivalence class with a single element
  -Merge two equivalence classes
  -Retrieve whether two elements are in the same equivalence class
  -Iterate on all the elements of the equivalence class of a given element
  -Iterate on all equivalence classes (and then within them)

Author:

    Julien Braine
    Arie Gurfinkel

Revision History:

*/

#include "ast/arith_decl_plugin.h"
#include "ast/for_each_expr.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/factor_equivs.h"

/**
   Factors input vector v into equivalence classes and the rest
 */
void factor_eqs(expr_ref_vector &v, expr_equiv_class &equiv) {
    ast_manager &m = v.get_manager();
    arith_util arith(m);
    expr *e1 = nullptr, *e2 = nullptr;

    flatten_and(v);
    unsigned j = 0;
    for (unsigned i = 0; i < v.size(); ++i) {
        if (m.is_eq(v.get(i), e1, e2)) {
            if (arith.is_zero(e1)) {
                std::swap(e1, e2);
            }

            // y + -1*x == 0
            expr* a0 = nullptr, *a1 = nullptr, *x = nullptr;
            if (arith.is_zero(e2) && arith.is_add(e1, a0, a1)) {
                if (arith.is_times_minus_one(a1, x)) {
                    e1 = a0;
                    e2 = x;
                }
                else if (arith.is_times_minus_one(a0, x)) {
                    e1 = a1;
                    e2 = x;
                }
            }
            equiv.merge(e1, e2);
        }
        else {
            if (j < i) {
                v[j] = v.get(i);
            }
            j++;
        }
    }
    v.shrink(j);
}

/**
 * Chooses a representative of an equivalence class
 */
expr *choose_rep(expr_equiv_class::eq_class &clazz, ast_manager &m) {
    expr *rep = nullptr;
    unsigned rep_sz = 0, elem_sz;
    for (expr *elem : clazz) {
        if (!m.is_value(elem)) {
            elem_sz = get_num_exprs(elem);
            if (!rep || (rep && rep_sz > elem_sz)) {
                rep = elem;
                rep_sz = elem_sz;
            }
        }
    }
    TRACE("equiv",
          tout << "Rep: " << mk_pp(rep, m) << "\n";
          for (expr *el : clazz)
              tout << mk_pp(el, m) << "\n";
          tout << "RepEnd\n";);

    return rep;
}

void rewrite_eqs (expr_ref_vector &v, expr_equiv_class &equiv) {
    ast_manager &m = v.m();
    expr_safe_replace sub(m);
    for (auto eq_class : equiv) {
        expr *rep = choose_rep(eq_class, m);
        for (expr *el : eq_class) {
            if (el != rep) {
                sub.insert (el, rep);
            }
        }
    }
    sub(v);
}


/**
 * converts equivalence classes to equalities
 */
void equiv_to_expr(expr_equiv_class &equiv, expr_ref_vector &out) {
    ast_manager &m = out.get_manager();
    for (auto eq_class : equiv) {
        expr *rep = choose_rep(eq_class, m);
        SASSERT(rep);
        for (expr *elem : eq_class) {
            if (rep != elem) {
                out.push_back (m.mk_eq (rep, elem));
            }
        }
    }
}

/**
 * expands equivalence classes to all derivable equalities
 */
bool equiv_to_expr_full(expr_equiv_class &equiv, expr_ref_vector &out) {
    ast_manager &m = out.get_manager();
    bool dirty = false;
    for (auto eq_class : equiv) {
        for (auto a = eq_class.begin(), end = eq_class.end(); a != end; ++a) {
            expr_equiv_class::iterator b(a);
            for (++b; b != end; ++b) {
                out.push_back(m.mk_eq(*a, *b));
                dirty = true;
            }
        }
    }
    return dirty;
}
