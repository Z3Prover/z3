/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    finite_set_simplifier.cpp

Abstract:

    See finite_set_simplifier.h.

--*/
#include "ast/simplifiers/finite_set_simplifier.h"
#include "ast/arith_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/finite_set_decl_plugin.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/var_subst.h"

struct finite_set_simplifier::rw_cfg : public default_rewriter_cfg {
    finite_set_simplifier& s;
    ast_manager& m;
    finite_set_util fs;
    arith_util arith;
    datatype_util dt;
    th_rewriter normalize;
    used_vars used;
    inv_var_shifter lower;
    var_subst subst;

    rw_cfg(finite_set_simplifier& s):
        s(s), m(s.m), fs(m), arith(m), dt(m), normalize(m, s.m_params),
        lower(m), subst(m) {}

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
        expr_ref field(m.mk_app(accessor, x), m);
        expr_ref value(m);
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
                // The projection may capture outer parameters, but not the candidate (#1).
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
            ++s.m_empty_domains;
            result = m.mk_true();
            return true;
        }
        expr_ref empty(fs.mk_empty(domain->get_sort()), m);
        expr_ref is_empty(m.mk_eq(domain, empty), m);
        // A nonempty finite image in a total arithmetic order attains its extrema.
        if (!all && is_extremum(q, domain)) {
            ++s.m_extrema;
            result = is_empty;
            return true;
        }
        if (!uses_bound_var(body)) {
            ++s.m_unused_vars;
            expr_ref condition = remove_binder(body);
            if (!all)
                condition = m.mk_not(condition);
            result = m.mk_or(is_empty, condition);
            return true;
        }
        expr_ref point(m);
        if (find_point(q, point)) {
            ++s.m_fixed_points;
            // Substitute in the lambda's scope, then lower all remaining outer
            // variables together. This also handles occurrences under binders.
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
            ++s.m_independent_guards;
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
                ++s.m_independent_guards;
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
        if (n == 2 && m.is_eq(f)) {
            for (unsigned i = 0; i < 2; ++i) {
                expr* predicate = nullptr, * domain = nullptr;
                expr* other = args[1 - i];
                if (!fs.is_filter(args[i], predicate, domain) || !is_lambda(predicate))
                    continue;
                auto* q = to_quantifier(predicate);
                if (q->get_num_decls() == 1 && (other == domain || fs.is_empty(other)) &&
                    bounded(other == domain, q, domain, result))
                    return BR_REWRITE_FULL;
            }
        }
        // Keep comparison atoms intact until fixed-point matching has inspected
        // their bounds; normalize arithmetic terms and datatype projections.
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

struct finite_set_simplifier::rw : public rewriter_tpl<rw_cfg> {
    rw_cfg cfg;
    rw(finite_set_simplifier& s):
        rewriter_tpl<rw_cfg>(s.m, false, cfg), cfg(s) {}
};

void finite_set_simplifier::reduce() {
    if (proofs_enabled())
        return;
    rw rewrite(*this);
    th_rewriter normalize(m, m_params);
    for (unsigned idx : indices()) {
        auto d = m_fmls[idx];
        expr_ref result(d.fml(), m), next(m);
        do {
            rewrite(result, next);
            normalize(next);
            if (next == result)
                break;
            result = next;
        } while (m.inc());
        if (result != d.fml())
            m_fmls.update(idx, dependent_expr(m, result, nullptr, d.dep()));
    }
}

void finite_set_simplifier::collect_statistics(statistics& st) const {
    st.update("finite-set-simplify-fixed-points", m_fixed_points);
    st.update("finite-set-simplify-unused-vars", m_unused_vars);
    st.update("finite-set-simplify-independent-guards", m_independent_guards);
    st.update("finite-set-simplify-empty-domains", m_empty_domains);
    st.update("finite-set-simplify-extrema", m_extrema);
}

void finite_set_simplifier::reset_statistics() {
    m_fixed_points = m_unused_vars = m_independent_guards = m_empty_domains = m_extrema = 0;
}

void finite_set_simplifier::collect_param_descrs(param_descrs& r) {
    th_rewriter::get_param_descrs(r);
}
