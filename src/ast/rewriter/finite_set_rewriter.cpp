/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_rewriter.cpp

Abstract:

    Rewriting Simplification for finite sets

Author:

    Nikolaj Bjorner (nbjorner) - October 2025

--*/

#include "ast/rewriter/finite_set_rewriter.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/var_subst.h"

namespace {
struct bounded_filter_cfg : public default_rewriter_cfg {
    ast_manager& m;
    finite_set_util fs;
    arith_util arith;
    datatype_util dt;
    th_rewriter normalize;
    used_vars used;
    inv_var_shifter lower;
    var_subst subst;

    bounded_filter_cfg(ast_manager& m, params_ref const& p):
        m(m), fs(m), arith(m), dt(m), normalize(m, p), lower(m), subst(m) {}

    bool uses_bound_var(expr* e) {
        used.reset();
        used.set_num_decls(1);
        used.process(e);
        return used.contains(0) != nullptr;
    }

    expr_ref remove_binder(expr* e) {
        expr_ref r(m);
        lower(e, 1, r);
        return r;
    }

    bool find_value(expr* body, expr* target, expr_ref& value) {
        expr_ref_vector conjuncts(m);
        flatten_and(body, conjuncts);
        obj_hashtable<expr> lower_bounds, upper_bounds;
        for (expr* e : conjuncts) {
            expr* a = nullptr, * b = nullptr;
            bool eq = m.is_eq(e, a, b);
            bool le = arith.is_le(e, a, b);
            bool ge = arith.is_ge(e, a, b);
            if (!eq && !le && !ge)
                continue;
            if (b == target) {
                std::swap(a, b);
                std::swap(le, ge);
            }
            if (a != target || b->get_sort() != target->get_sort() || uses_bound_var(b))
                continue;
            if (eq || (le && lower_bounds.contains(b)) || (ge && upper_bounds.contains(b))) {
                value = b;
                return true;
            }
            if (le)
                upper_bounds.insert(b);
            else
                lower_bounds.insert(b);
        }
        return false;
    }

    bool find_point(quantifier* q, expr_ref& point) {
        sort* sort = q->get_decl_sort(0);
        expr_ref x(m.mk_var(0, sort), m);
        if (find_value(q->get_expr(), x, point))
            return true;
        if (!dt.is_datatype(sort))
            return false;
        auto const& constructors = *dt.get_datatype_constructors(sort);
        if (constructors.size() != 1 || constructors[0]->get_arity() != 1)
            return false;
        func_decl* constructor = constructors[0];
        func_decl* accessor = (*dt.get_constructor_accessors(constructor))[0];
        expr_ref field(m.mk_app(accessor, x), m), value(m);
        if (!find_value(q->get_expr(), field, value))
            return false;
        point = m.mk_app(constructor, value);
        return true;
    }

    bool is_extremum(quantifier* q, expr* domain) {
        expr* lhs = nullptr, * rhs = nullptr;
        if (!m.is_eq(q->get_expr(), lhs, rhs))
            return false;
        var_shifter lift(m);
        expr_ref lifted_domain(m);
        lift(domain, 1, lifted_domain);
        for (unsigned i = 0; i < 2; ++i) {
            expr* predicate = nullptr, * inner_domain = nullptr;
            if (!fs.is_filter(i == 0 ? lhs : rhs, predicate, inner_domain) ||
                inner_domain != (i == 0 ? rhs : lhs) ||
                inner_domain != lifted_domain || !is_lambda(predicate))
                continue;
            auto* inner = to_quantifier(predicate);
            expr* a = nullptr, * b = nullptr;
            if (inner->get_num_decls() != 1 ||
                (!arith.is_le(inner->get_expr(), a, b) && !arith.is_ge(inner->get_expr(), a, b)))
                continue;
            if (!arith.is_int(a) && !arith.is_real(a))
                continue;
            for (unsigned j = 0; j < 2; ++j) {
                if (j == 1)
                    std::swap(a, b);
                used.reset();
                used.set_num_decls(2);
                used.process(a);
                // Outer parameters are allowed, but the projection cannot depend on the candidate.
                if (!used.contains(0) || used.contains(1))
                    continue;
                expr_ref candidate(m.mk_var(1, q->get_decl_sort(0)), m);
                if (subst(a, candidate) == b)
                    return true;
            }
        }
        return false;
    }

    bool bounded(bool all, quantifier* q, expr* domain, expr_ref& result) {
        expr* body = q->get_expr();
        if (fs.is_empty(domain)) {
            result = m.mk_true();
            return true;
        }
        expr_ref empty(fs.mk_empty(domain->get_sort()), m);
        expr_ref is_empty(m.mk_eq(domain, empty), m);
        // A nonempty finite image in a total arithmetic order attains its extrema.
        if (!all && is_extremum(q, domain)) {
            result = is_empty;
            return true;
        }
        if (!uses_bound_var(body)) {
            expr_ref condition = remove_binder(body);
            if (!all)
                condition = m.mk_not(condition);
            result = m.mk_or(is_empty, condition);
            return true;
        }
        expr_ref point(m);
        if (find_point(q, point)) {
            // Substitute in the lambda's scope before lowering outer variables,
            // including occurrences under nested binders.
            expr_ref condition = subst(body, point);
            condition = remove_binder(condition);
            point = remove_binder(point);
            expr_ref constraint(m);
            if (all) {
                expr_ref singleton(fs.mk_singleton(point), m);
                constraint = m.mk_eq(domain, singleton);
                constraint = m.mk_and(constraint, condition);
                result = m.mk_or(is_empty, constraint);
            }
            else {
                constraint = fs.mk_in(point, domain);
                constraint = m.mk_and(constraint, condition);
                result = m.mk_not(constraint);
            }
            return true;
        }
        expr* guard = nullptr, * consequent = nullptr;
        if (all && m.is_implies(body, guard, consequent) && !uses_bound_var(guard)) {
            expr_ref lifted = remove_binder(guard);
            expr_ref negated(m.mk_not(lifted), m);
            quantifier_ref predicate(m.update_quantifier(q, consequent), m);
            expr_ref filtered(fs.mk_filter(predicate, domain), m);
            expr_ref rest(m.mk_eq(filtered, domain), m);
            result = m.mk_or(negated, rest);
            return true;
        }
        if ((all && m.is_or(body)) || (!all && m.is_and(body))) {
            expr_ref_vector independent(m), dependent(m);
            for (expr* arg : *to_app(body))
                (uses_bound_var(arg) ? dependent : independent).push_back(arg);
            if (!independent.empty() && !dependent.empty()) {
                expr_ref guard = all ? mk_or(independent) : mk_and(independent);
                guard = remove_binder(guard);
                if (!all)
                    guard = m.mk_not(guard);
                expr_ref rest_body = all ? mk_or(dependent) : mk_and(dependent);
                quantifier_ref predicate(m.update_quantifier(q, rest_body), m);
                expr_ref filtered(fs.mk_filter(predicate, domain), m);
                expr_ref rest(m.mk_eq(filtered, all ? domain : empty.get()), m);
                result = m.mk_or(guard, rest);
                return true;
            }
        }
        return false;
    }

    br_status reduce_app(func_decl* f, unsigned n, expr* const* args, expr_ref& result, proof_ref&) {
        // Preserve comparison atoms for bound matching, while simplifying their terms.
        if ((f->get_family_id() == arith.get_family_id() && !m.is_bool(f->get_range())) ||
            f->get_family_id() == dt.get_family_id()) {
            result = normalize.mk_app(f, n, args);
            if (!is_app(result) || to_app(result)->get_decl() != f ||
                !std::equal(args, args + n, to_app(result)->begin(), to_app(result)->end()))
                return BR_DONE;
        }
        return BR_FAILED;
    }
};
}

br_status finite_set_rewriter::mk_eq_bounded(expr* a, expr* b, expr_ref& result) {
    for (unsigned i = 0; i < 2; ++i) {
        expr* predicate = nullptr, * domain = nullptr;
        expr* other = i == 0 ? b : a;
        if (!u.is_filter(i == 0 ? a : b, predicate, domain) || !is_lambda(predicate))
            continue;
        auto* q = to_quantifier(predicate);
        if (q->get_num_decls() != 1 || (other != domain && !u.is_empty(other)))
            continue;
        bounded_filter_cfg cfg(m, m_params);
        rewriter_tpl<bounded_filter_cfg> terms(m, false, cfg);
        expr_ref body(m);
        terms(q->get_expr(), body);
        quantifier_ref normalized(m.update_quantifier(q, body), m);
        if (!cfg.bounded(other == domain, normalized, domain, result))
            continue;
        th_rewriter normalize(m, m_params);
        normalize(result);
        return BR_REWRITE_FULL;
    }
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    
    switch (f->get_decl_kind()) {
    case OP_FINITE_SET_UNION:
        return mk_union(num_args, args, result);
    case OP_FINITE_SET_INTERSECT:
        return mk_intersect(num_args, args, result);
    case OP_FINITE_SET_DIFFERENCE:
        SASSERT(num_args == 2);
        return mk_difference(args[0], args[1], result);
    case OP_FINITE_SET_SUBSET:
        SASSERT(num_args == 2);
        return mk_subset(args[0], args[1], result);
    case OP_FINITE_SET_SINGLETON:
        SASSERT(num_args == 1);
        return mk_singleton(args[0], result);
    case OP_FINITE_SET_IN:
        SASSERT(num_args == 2);
        return mk_in(args[0], args[1], result);
    case OP_FINITE_SET_SIZE:
        return mk_size(args[0], result);
    case OP_FINITE_SET_MAP:
        SASSERT(num_args == 2);
        return mk_map(args[0], args[1], result);
    case OP_FINITE_SET_FILTER:
        SASSERT(num_args == 2);
        return mk_filter(args[0], args[1], result);
    default:
        return BR_FAILED;
    }
}

br_status finite_set_rewriter::mk_union(unsigned num_args, expr * const * args, expr_ref & result) {
    VERIFY(num_args == 2);
    // Idempotency: set.union(x, x) -> x
    if (args[0] == args[1]) {
        result = args[0];
        return BR_DONE;
    }
    
    // Identity: set.union(x, empty) -> x or set.union(empty, x) -> x
    if (u.is_empty(args[0])) {
        result = args[1];
        return BR_DONE;
    }
    if (u.is_empty(args[1])) {
        result = args[0];
        return BR_DONE;
    }

    // Absorption: set.union(x, set.intersect(x, y)) -> x
    expr *a1, *a2;
    if (u.is_intersect(args[1], a1, a2)) {
        if (args[0] == a1 || args[0] == a2) {
            result = args[0];
            return BR_DONE;
        }
    }

    // Absorption: set.union(set.intersect(x, y), x) -> x
    if (u.is_intersect(args[0], a1, a2)) {
        if (args[1] == a1 || args[1] == a2) {
            result = args[1];
            return BR_DONE;
        }
    }
    
    
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_intersect(unsigned num_args, expr * const * args, expr_ref & result) {
    if (num_args != 2)
        return BR_FAILED;

    // Idempotency: set.intersect(x, x) -> x
    if (args[0] == args[1]) {
        result = args[0];
        return BR_DONE;
    }
    
    // Annihilation: set.intersect(x, empty) -> empty or set.intersect(empty, x) -> empty
    if (u.is_empty(args[0])) {
        result = args[0];
        return BR_DONE;
    }
    if (u.is_empty(args[1])) {
        result = args[1];
        return BR_DONE;
    }

    // Absorption: set.intersect(x, set.union(x, y)) -> x
    expr *a1, *a2;
    if (u.is_union(args[1], a1, a2)) {
        if (args[0] == a1 || args[0] == a2) {
            result = args[0];
            return BR_DONE;
        }
    }

    // Absorption: set.intersect(set.union(x, y), x) -> x
    if (u.is_union(args[0], a1, a2)) {
        if (args[1] == a1 || args[1] == a2) {
            result = args[1];
            return BR_DONE;
        }
    }
    expr *l1, *l2, *u1, *u2;
    if (u.is_range(args[0], l1, u1) && u.is_range(args[1], l2, u2)) {
        arith_util a(m);
        auto max_l = m.mk_ite(a.mk_ge(l1, l2), l1, l2);
        auto min_u = m.mk_ite(a.mk_ge(u1, u2), u2, u1);
        result = u.mk_range(max_l, min_u);
        return BR_REWRITE_FULL;
    }
    
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_difference(expr * arg1, expr * arg2, expr_ref & result) {
    // set.difference(x, x) -> set.empty
    if (arg1 == arg2) {
        sort* set_sort = arg1->get_sort();
        SASSERT(u.is_finite_set(set_sort));
        result = u.mk_empty(set_sort);
        return BR_DONE;
    }
    
    // Identity: set.difference(x, empty) -> x
    if (u.is_empty(arg2)) {
        result = arg1;
        return BR_DONE;
    }
    
    // Annihilation: set.difference(empty, x) -> empty
    if (u.is_empty(arg1)) {
        result = arg1;
        return BR_DONE;
    }
    
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_subset(expr * arg1, expr * arg2, expr_ref & result) {
    // set.subset(x, x) -> true
    if (arg1 == arg2) {
        result = m.mk_true();
        return BR_DONE;
    }
    
    // set.subset(empty, x) -> true
    if (u.is_empty(arg1)) {
        result = m.mk_true();
        return BR_DONE;
    }
    
    // set.subset(x, empty) -> x = empty
    if (u.is_empty(arg2)) {
        result = m.mk_eq(arg1, arg2);
        return BR_REWRITE1;
    }
    
    // General case: set.subset(x, y) -> set.intersect(x, y) = x
    expr_ref intersect(m);
    intersect = u.mk_intersect(arg1, arg2);
    result = m.mk_eq(intersect, arg1);
    return BR_REWRITE3;
}

br_status finite_set_rewriter::mk_singleton(expr * arg, expr_ref & result) {
    // Singleton is already in normal form, no simplifications
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_size(expr * arg, expr_ref & result) {
    arith_util a(m);
    if (u.is_empty(arg)) {
        // size(empty) -> 0
        result = a.mk_int(0);
        return BR_DONE;
    }
    if (u.is_singleton(arg)) {
        // size(singleton(x)) -> 1
        result = a.mk_int(1);
        return BR_DONE;
    }
    expr *lower, *upper;
    if (u.is_range(arg, lower, upper)) {
        // size(range(a, b)) -> b - a + 1
        expr_ref size_expr(m);
        {
            auto _seq207_0 = a.mk_sub(upper, lower);
            auto _seq207_1 = a.mk_int(1);
            size_expr = a.mk_add(_seq207_0, _seq207_1);
        }
        {
            auto _seq208_0 = a.mk_gt(lower, upper);
            auto _seq208_1 = a.mk_int(0);
            result = m.mk_ite(_seq208_0, _seq208_1, size_expr);
        }
        return BR_REWRITE3;
    }
    // Size is already in normal form, no simplifications
    return BR_FAILED;
}

// set.map(f, set.empty) -> set.empty
// set.map(f, set.singleton(x)) -> set.singleton(f(x))
// set.map(f, set.union(s, t)) -> set.union(set.map(f, s), set.map(f, t))
// NB. set.map does not distribute over set.intersect or set.difference:
// f is not required to be injective, so set.map(f, s) can contain elements
// whose pre-images are all outside of s. For example with f = (lambda (x) 0),
// s = {1}, t = {2}: set.map(f, set.intersect(s, t)) is empty while
// set.intersect(set.map(f, s), set.map(f, t)) is {0}, and
// set.map(f, set.difference(s, t)) is {0} while
// set.difference(set.map(f, s), set.map(f, t)) is empty.
br_status finite_set_rewriter::mk_map(expr * f, expr * set, expr_ref & result) {
    if (u.is_empty(set)) {
        sort *set_sort = u.mk_finite_set_sort(get_array_range(f->get_sort()));
        result = u.mk_empty(set_sort);
        return BR_DONE;
    }
    expr *x = nullptr;
    if (u.is_singleton(set, x)) {
        array_util autil(m);
        result = u.mk_singleton(autil.mk_select(f, x));
        return BR_REWRITE2;
    }
    expr *s = nullptr, *t = nullptr;
    if (u.is_union(set, s, t)) {
        expr_ref lhs(u.mk_map(f, s), m);
        expr_ref rhs(u.mk_map(f, t), m);
        result = u.mk_union(lhs, rhs);
        return BR_REWRITE2;
    }
    return BR_FAILED;
}

// set.filter(p, set.empty) -> set.empty
// set.filter(p, set.singleton(x)) -> ite(p(x), set.singleton(x), set.empty)
// set.filter(p, set.union(s, t)) -> set.union(set.filter(p, s), set.filter(p, t))
// set.filter(p, set.intersect(s, t)) -> set.intersect(set.filter(p, s), set.filter(p, t))
// set.filter(p, set.difference(s, t)) -> set.difference(set.filter(p, s), set.filter(p, t))
br_status finite_set_rewriter::mk_filter(expr * p, expr * set, expr_ref & result) {
    if (u.is_empty(set)) {
        result = set;
        return BR_DONE;
    }
    expr *x = nullptr;
    if (u.is_singleton(set, x)) {
        array_util autil(m);
        expr_ref pred(autil.mk_select(p, x), m);
        result = m.mk_ite(pred, set, u.mk_empty(set->get_sort()));
        return BR_REWRITE2;
    }
    expr *s = nullptr, *t = nullptr;
    if (u.is_union(set, s, t)) {
        expr_ref lhs(u.mk_filter(p, s), m);
        expr_ref rhs(u.mk_filter(p, t), m);
        result = u.mk_union(lhs, rhs);
        return BR_REWRITE2;
    }
    // set.filter is a pointwise restriction, so it distributes over
    // set.intersect and set.difference.
    if (u.is_intersect(set, s, t)) {
        expr_ref lhs(u.mk_filter(p, s), m);
        expr_ref rhs(u.mk_filter(p, t), m);
        result = u.mk_intersect(lhs, rhs);
        return BR_REWRITE2;
    }
    if (u.is_difference(set, s, t)) {
        expr_ref lhs(u.mk_filter(p, s), m);
        expr_ref rhs(u.mk_filter(p, t), m);
        result = u.mk_difference(lhs, rhs);
        return BR_REWRITE2;
    }
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_in(expr * elem, expr * set, expr_ref & result) {
    // set.in(x, empty) -> false
    if (u.is_empty(set)) {
        result = m.mk_false();
        return BR_DONE;
    }
    
    // set.in(x, singleton(y)) checks
    expr* singleton_elem;
    if (u.is_singleton(set, singleton_elem)) {
        // set.in(x, singleton(x)) -> true (when x is the same)
        if (elem == singleton_elem) {
            result = m.mk_true();
            return BR_DONE;
        }
        // set.in(x, singleton(y)) -> x = y (when x != y)
        result = m.mk_eq(elem, singleton_elem);
        return BR_REWRITE1;
    }
    expr *lo = nullptr, *hi = nullptr;
    if (u.is_range(set, lo, hi)) {
        arith_util a(m);
        {
            auto _seq237_0 = a.mk_le(lo, elem);
            auto _seq237_1 = a.mk_le(elem, hi);
            result = m.mk_and(_seq237_0, _seq237_1);
        }
        return BR_REWRITE2;
    }
    // NB we don't rewrite (set.in x (set.union s t)) to (or (set.in x s) (set.in x t))
    // because it creates two new sub-expressions. The expression (set.union s t) could
    // be shared with other expressions so the net effect of this rewrite could be to create
    // a larger formula for the solver.
    return BR_FAILED;
}


/**
* if a, b are set expressions we can create an on-the-fly heap for their min-elements
* a, b are normalized to the form (set.union s t) or (set.empty) where 
* s is a singleton or range expression such that every element in t are above s.
* we distinguish numerical values from value expressions:
* - for numerical values we use the ordering over numerals to pick minimal ranges
* - for unique value expressions ranging over non-numerals use expression identifiers
* - for other expressions use identifiers to sort expressions, but make sure to be inconclusive
*   for set difference
* We want mk_eq_core to produce a result true/false if the arguments are both (unique) values.
* This allows to evaluate models for being well-formed conclusively.
* 
* A way to convert a set expression to a heap is as follows:
* 
* min({s}) = {s} u {}
* min({}) = {}
* min([l..u]) = [l..u] u {}
* min(s u t) = 
*   let {x} u s1 = min(s)
*   let {y} u t1 = min(t)
*   if x = y then
*        { x } u (s1 u t1)
*   else  if x < y then 
*        {x} u (s1 u ({y} u t1)
*   else // x > y 
*        {y} u (t1 u ({x} u s1)
*   
*  Handling ranges is TBD
*  For proper range handling we have to change is_less on numeric singleton sets
*  to use the numerical value, not the expression identifier. Then the ordering
*  has to make all numeric values less than symbolic values.
*/

bool finite_set_rewriter::is_less(expr *a, expr *b) {
    return a->get_id() < b->get_id();
}

expr* finite_set_rewriter::mk_union(expr* a, expr* b) {
    if (u.is_empty(a))
        return b;
    if (u.is_empty(b))
        return a;
    if (a == b)
        return a;
    return u.mk_union(a, b);
}

expr* finite_set_rewriter::min(expr* e) {
    if (m_is_min.is_marked(e))
        return e;
    expr *a = nullptr, *b = nullptr;
    if (u.is_union(e, a, b)) {
        a = min(a);
        b = min(b);
        if (u.is_empty(a))
            return b;
        if (u.is_empty(b))
            return a;
        auto [x,a1] = get_min(a);
        auto [y,b1] = get_min(b);
        if (x == y)
            a = mk_union(x, mk_union(a1, b1));
        else if (is_less(x, y))
            a = mk_union(x, mk_union(a1, b));
        else
            a = mk_union(y, mk_union(a, b1));
        m_pinned.push_back(a);
        m_is_min.mark(a);
        return a;
    }
    if (u.is_intersect(e, a, b)) {
        if (!from_unique_values(a) || !from_unique_values(b)) {
            m_pinned.push_back(e);
            m_is_min.mark(e);
            return e;
        }
        while (true) {
            a = min(a);
            b = min(b);
            if (u.is_empty(a))
                return a;
            if (u.is_empty(b))
                return b;
            auto [x, a1] = get_min(a);
            auto [y, b1] = get_min(b);
            if (x == y) {
                a = mk_union(x, u.mk_intersect(a1, b1));
                m_pinned.push_back(a);
                m_is_min.mark(a);
                return a;
            }
            else if (is_less(x, y))
                a = a1;
            else
                b = b1;
        }
    }
    if (u.is_difference(e, a, b)) {
        if (!from_unique_values(a) || !from_unique_values(b)) {
            m_pinned.push_back(e);
            m_is_min.mark(e);
            return e;
        }
        while (true) {
            a = min(a);
            b = min(b);
            if (u.is_empty(a) || u.is_empty(b))
                return a;
            auto [x, a1] = get_min(a);
            auto [y, b1] = get_min(b);
            if (x == y) {
                a = a1;
                b = b1;
            }
            else if (is_less(x, y)) {
                a = mk_union(x, u.mk_difference(a1, b));
                m_pinned.push_back(a);
                m_is_min.mark(a);
                return a;
            }
            else {
                b = b1;
            }
        }
    }
    // set.filter, set.map don't have decompositions
    m_pinned.push_back(e);
    m_is_min.mark(e);
    return e;
}

std::pair<expr*, expr*> finite_set_rewriter::get_min(expr* a) {
    expr *x = nullptr, *y = nullptr;
    if (u.is_union(a, x, y))
        return {x, y};
    auto empty = u.mk_empty(a->get_sort());
    m_pinned.push_back(empty);
    return {a, empty};
}

br_status finite_set_rewriter::mk_eq_core(expr *a, expr *b, expr_ref &result) {
    if (a != b) {
        br_status st = mk_eq_bounded(a, b, result);
        if (st != BR_FAILED)
            return st;
    }
    m_is_min.reset();
    m_pinned.reset();
    bool are_unique = true;
    while (true) {
        if (a == b) {
            result = m.mk_true();
            return BR_DONE;
        }
        TRACE(finite_set, tout << mk_pp(a, m) << " == " << mk_pp(b, m) << "\n");
        a = min(a);
        b = min(b);
        auto [x, a1] = get_min(a);
        auto [y, b1] = get_min(b);

        // only empty sets and singletons of unique values are unique.
        // ranges are not counted as unique.
        are_unique &= m.is_unique_value(x) && m.is_unique_value(y);
        a = a1;
        b = b1;
        if (x == y)
            continue;

        if (m.are_distinct(x, y) && are_unique) {
            are_unique &= from_unique_values(a);
            are_unique &= from_unique_values(b);
            if (are_unique) {
                result = m.mk_false();
                return BR_DONE;
            }
        }
        return BR_FAILED;
    }
}

bool finite_set_rewriter::from_unique_values(expr *a) {
    while (!u.is_empty(a)) {
        auto [x, a1] = get_min(min(a));
        if (!m.is_unique_value(x))
            return false;
        a = a1;
    }
    return true;
}
