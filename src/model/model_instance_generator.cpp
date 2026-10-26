/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    model_instance_generator.cpp

Abstract:

    Array and datatype witnesses for model-based quantifier instantiation.

--*/

#include "model/model_instance_generator.h"
#include "ast/ast_util.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/for_each_expr.h"
#include "ast/has_free_vars.h"
#include "ast/occurs.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/var_subst.h"

model_instance_generator::model_instance_generator(context& ctx):
    m_context(ctx),
    m(ctx.get_model().get_manager()),
    m_array(m),
    m_terms(m) {}

bool model_instance_generator::is_auxiliary(expr* e) const {
    for (expr* t : subterms::all(expr_ref(e, m)))
        if (m.is_model_value(t) || (is_app(t) && m_context.is_auxiliary(to_app(t)->get_decl())))
            return true;
    return false;
}

void model_instance_generator::collect_values(quantifier* q, sort* s, expr_ref_vector& values) const {
    for (expr* t : subterms::ground(expr_ref(q->get_expr(), m))) {
        if (values.size() >= 4)
            break;
        if (is_app(t) && is_ground(t) && t->get_sort() == s)
            values.push_back(t);
    }
}

bool model_instance_generator::repair_bindings(expr_ref_vector& bindings) const {
    for (unsigned i = 0; i < bindings.size(); ++i) {
        expr* b = bindings.get(i);
        if (!is_app(b) || to_app(b)->get_num_args() != 0 ||
            !m.is_uninterp(b->get_sort()) || !is_auxiliary(b))
            continue;
        expr* replacement = nullptr;
        for (expr* t : m_terms)
            if (is_app(t) && is_ground(t) && t->get_sort() == b->get_sort() && !is_auxiliary(t)) {
                replacement = t;
                break;
            }
        if (!replacement)
            return false;
        bindings[i] = replacement;
    }
    return true;
}

void model_instance_generator::add_lambda_instances(quantifier* q, expr_ref_vector const& bindings) {
    bool has_lambda = false;
    for (expr* t : subterms::all(expr_ref(q->get_expr(), m)))
        if (is_lambda(t)) {
            has_lambda = true;
            break;
        }
    if (!has_lambda)
        return;
    for (unsigned i = 0; i < bindings.size(); ++i) {
        sort* s = bindings.get(i)->get_sort();
        if (!m_array.is_array(s))
            continue;
        expr_ref_vector values(m);
        collect_values(q, get_array_range(s), values);
        if (values.empty())
            continue;
        expr_ref placeholder(m.mk_fresh_const("mbqi_f", s), m);
        expr_ref_vector subst(bindings);
        subst[i] = placeholder;
        expr_ref body = instantiate(m, q, subst.data());
        unsigned num_lambdas = 0;
        for (expr* t : subterms::all(body)) {
            if (!is_lambda(t) || t->get_sort() != s || has_free_vars(t))
                continue;
            if (num_lambdas >= 2)
                break;
            bool has_select = false;
            for (expr* u : subterms::all(expr_ref(to_quantifier(t)->get_expr(), m)))
                if (m_array.is_select(u) && to_app(u)->get_arg(0) == placeholder) {
                    has_select = true;
                    break;
                }
            if (!has_select)
                continue;
            ++num_lambdas;
            for (expr* v : values) {
                struct select_cfg : default_rewriter_cfg {
                    array_util& a;
                    expr* placeholder;
                    expr* value;
                    select_cfg(array_util& a, expr* p, expr* v): a(a), placeholder(p), value(v) {}
                    br_status reduce_app(func_decl* f, unsigned n, expr* const* args, expr_ref& result, proof_ref&) {
                        if (!a.is_select(f) || n == 0 || args[0] != placeholder)
                            return BR_FAILED;
                        result = value;
                        return BR_DONE;
                    }
                };
                select_cfg cfg(m_array, placeholder, v);
                rewriter_tpl<select_cfg> rw(m, false, cfg);
                expr_ref candidate(m);
                rw(t, candidate);
                if (occurs(placeholder, candidate))
                    continue;
                expr_ref_vector alt(bindings);
                alt[i] = candidate;
                m_context.add_instance(q, alt);
            }
        }
    }
}

void model_instance_generator::add_datatype_instances(quantifier* q, expr_ref_vector const& bindings) {
    datatype::util dt(m);
    for (unsigned i = 0; i < bindings.size(); ++i) {
        expr* b = bindings.get(i);
        if (!is_app(b) || !dt.is_datatype(b->get_sort()) || !dt.is_constructor(to_app(b)))
            continue;
        app* cons = to_app(b);
        for (unsigned k = 0; k < cons->get_num_args(); ++k) {
            sort* s = cons->get_arg(k)->get_sort();
            if (!m_array.is_array(s))
                continue;
            expr_ref_vector values(m);
            collect_values(q, get_array_range(s), values);
            for (expr* v : values) {
                expr_ref_vector args(m);
                for (unsigned j = 0; j < cons->get_num_args(); ++j)
                    args.push_back(j == k ? m_array.mk_const_array(s, v) : cons->get_arg(j));
                expr_ref_vector alt(bindings);
                alt[i] = m.mk_app(cons->get_decl(), args.size(), args.data());
                m_context.add_instance(q, alt);
            }
        }
    }
}

void model_instance_generator::add_guarded_instances(quantifier* q, expr_ref_vector const& bindings) {
    for (unsigned i = 0; i < bindings.size(); ++i) {
        sort* s = bindings.get(i)->get_sort();
        if (!m_array.is_array(s) || get_array_arity(s) != 1)
            continue;
        bool has_array = false;
        model_core& mdl = m_context.get_model();
        for (unsigned j = 0; j < mdl.get_num_constants(); ++j) {
            func_decl* c = mdl.get_constant(j);
            if (c->get_range() == s && !m_context.is_auxiliary(c)) {
                has_array = true;
                break;
            }
        }
        if (has_array)
            continue;
        if (!m_terms_initialized) {
            m_context.get_terms(m_terms);
            m_terms_initialized = true;
        }
        expr_ref_vector fixed(bindings);
        if (!repair_bindings(fixed))
            continue;
        expr_ref_vector values(m);
        collect_values(q, get_array_range(s), values);
        expr_mark seen;
        for (expr* v : values)
            seen.mark(v, true);
        for (expr* t : m_terms) {
            if (values.size() >= 6)
                break;
            if (is_app(t) && is_ground(t) && t->get_sort() == get_array_range(s) &&
                !seen.is_marked(t) && !is_auxiliary(t)) {
                seen.mark(t, true);
                values.push_back(t);
            }
        }
        if (values.empty())
            continue;
        expr_ref placeholder(m.mk_fresh_const("mbqi_g", s), m);
        expr_ref_vector subst(fixed);
        subst[i] = placeholder;
        expr_ref body = instantiate(m, q, subst.data());
        unsigned num_found = 0;
        sort* dom = get_array_domain(s, 0);
        // Do not extract a guard from a surrounding binder's scope.
        for (expr* t : subterms::ground(body)) {
            if (num_found >= 2)
                break;
            expr* inner = t;
            bool under_forall = is_forall(t);
            if (under_forall) {
                quantifier* quant = to_quantifier(t);
                if (quant->get_num_decls() != 1 || quant->get_decl_sort(0) != dom)
                    continue;
                inner = quant->get_expr();
            }
            expr* guard = nullptr, * eq = nullptr, * c = nullptr, * a = nullptr, * b = nullptr;
            if (m.is_ite(inner, c, a, b)) {
                guard = c;
                eq = b;
            }
            else if (m.is_implies(inner, c, a) && m.is_not(c, c)) {
                guard = c;
                eq = a;
            }
            else if (m.is_or(inner) && to_app(inner)->get_num_args() == 2) {
                expr* o0 = to_app(inner)->get_arg(0), * o1 = to_app(inner)->get_arg(1);
                if (m.is_eq(o1) && m.is_not(o0, c)) { guard = c; eq = o1; }
                else if (m.is_eq(o0) && m.is_not(o1, c)) { guard = c; eq = o0; }
                else if (m.is_eq(o1)) { guard = o0; eq = o1; }
                else if (m.is_eq(o0)) { guard = o1; eq = o0; }
            }
            expr* lhs = nullptr, * rhs = nullptr, * d = nullptr, * idx = nullptr;
            if (!guard || !eq || !m.is_eq(eq, lhs, rhs))
                continue;
            if (m_array.is_select(lhs) && to_app(lhs)->get_arg(0) == placeholder) {
                d = rhs;
                idx = to_app(lhs)->get_arg(1);
            }
            else if (m_array.is_select(rhs) && to_app(rhs)->get_arg(0) == placeholder) {
                d = lhs;
                idx = to_app(rhs)->get_arg(1);
            }
            if (!d || occurs(placeholder, d) || !is_ground(d))
                continue;
            if (under_forall ? (!is_var(idx) || to_var(idx)->get_idx() != 0) : !is_ground(idx))
                continue;
            bool has_binders = false;
            for (expr* u : subterms::all(expr_ref(guard, m)))
                if (is_quantifier(u)) {
                    has_binders = true;
                    break;
                }
            if (has_binders)
                continue;
            expr_ref guard_body(guard, m);
            if (!under_forall) {
                expr_safe_replace rep(m);
                expr_ref x(m.mk_var(0, dom), m);
                rep.insert(idx, x);
                rep(guard, guard_body);
            }
            if (occurs(placeholder, guard_body))
                continue;
            ++num_found;
            for (expr* v : values) {
                if (v == d)
                    continue;
                expr_ref lambda_body(m.mk_ite(guard_body, v, d), m);
                symbol name("x");
                expr_ref_vector alt(fixed);
                alt[i] = m.mk_lambda(1, &dom, &name, lambda_body);
                m_context.add_instance(q, alt);
            }
        }
    }
}

void model_instance_generator::add_store_instances(quantifier* q, expr_ref_vector const& bindings, ptr_vector<func_decl> const& bases) {
    for (unsigned i = 0; i < bindings.size(); ++i) {
        sort* s = bindings.get(i)->get_sort();
        if (!m_array.is_array(s) || get_array_arity(s) != 1)
            continue;
        func_decl* base_decl = bases[i];
        if (!base_decl) {
            model_core& mdl = m_context.get_model();
            for (unsigned j = 0; j < mdl.get_num_constants(); ++j) {
                func_decl* c = mdl.get_constant(j);
                if (c->get_range() == s && !m_context.is_auxiliary(c)) {
                    base_decl = c;
                    break;
                }
            }
        }
        if (!base_decl)
            continue;
        expr_ref_vector values(m);
        collect_values(q, get_array_range(s), values);
        expr_ref base(m.mk_const(base_decl), m);
        for (unsigned j = 0; j < bindings.size(); ++j) {
            if (j == i || bindings.get(j)->get_sort() != get_array_domain(s, 0))
                continue;
            for (expr* v : values) {
                expr* args[3] = { base, bindings.get(j), v };
                expr_ref_vector alt(bindings);
                alt[i] = m_array.mk_store(3, args);
                m_context.add_instance(q, alt);
            }
        }
    }
}

void model_instance_generator::operator()(quantifier* q, expr_ref_vector const& bindings, ptr_vector<func_decl> const& bases) {
    SASSERT(q->get_num_decls() == bindings.size());
    SASSERT(bindings.size() == bases.size());
    add_store_instances(q, bindings, bases);
    add_lambda_instances(q, bindings);
    add_datatype_instances(q, bindings);
    add_guarded_instances(q, bindings);
}

expr_ref model_instance_generator::mk_store_instance(func_decl* f, model_core& cex, func_decl*& base) {
    expr_ref result(m);
    base = nullptr;
    func_interp* fi = cex.get_func_interp(f);
    if (!fi || f->get_arity() == 0)
        return result;
    sort* s = m_array.mk_array_sort(f->get_arity(), f->get_domain(), f->get_range());
    model_core& mdl = m_context.get_model();
    unsigned best_cost = UINT_MAX;
    for (unsigned i = 0; i < mdl.get_num_constants(); ++i) {
        func_decl* c = mdl.get_constant(i);
        if (c->get_range() != s || m_context.is_auxiliary(c))
            continue;
        expr* val = mdl.get_const_interp(c);
        func_decl* g = nullptr;
        func_interp* fa = val && m_array.is_as_array(val, g) ? mdl.get_func_interp(g) : nullptr;
        unsigned cost = 0;
        for (unsigned k = 0; k < fi->num_entries(); ++k) {
            func_entry const* e = fi->get_entry(k);
            func_entry* ea = fa ? fa->get_entry(e->get_args()) : nullptr;
            if (!ea || ea->get_result() != e->get_result())
                ++cost;
        }
        if (cost < best_cost) {
            base = c;
            best_cost = cost;
        }
    }
    if (!base)
        return result;
    result = m.mk_const(base);
    expr* val = mdl.get_const_interp(base);
    func_decl* g = nullptr;
    func_interp* fa = val && m_array.is_as_array(val, g) ? mdl.get_func_interp(g) : nullptr;
    expr_ref_vector args(m);
    for (unsigned k = 0; k < fi->num_entries(); ++k) {
        func_entry const* e = fi->get_entry(k);
        func_entry* ea = fa ? fa->get_entry(e->get_args()) : nullptr;
        if (ea && ea->get_result() == e->get_result())
            continue;
        args.reset();
        args.push_back(result);
        args.append(f->get_arity(), e->get_args());
        args.push_back(e->get_result());
        result = m_array.mk_store(args);
    }
    return m_context.rewrite_value(result);
}

expr_ref model_instance_generator::as_array_to_stores(expr* e, model_core& cex) {
    struct array_cfg : default_rewriter_cfg {
        ast_manager& m;
        model_core& cex;
        array_util array;
        expr_ref_vector trail;
        bool changed = false;
        array_cfg(ast_manager& m, model_core& cex): m(m), cex(cex), array(m), trail(m) {}
        bool get_subst(expr* e, expr*& t, proof*& pr) {
            t = nullptr;
            pr = nullptr;
            func_decl* f = nullptr;
            if (!array.is_as_array(e, f))
                return false;
            func_interp* fi = cex.get_func_interp(f);
            if (!fi || !fi->get_else() || !is_ground(fi->get_else()))
                return false;
            expr_ref r(array.mk_const_array(e->get_sort(), fi->get_else()), m);
            expr_ref_vector args(m);
            for (unsigned i = 0; i < fi->num_entries(); ++i) {
                func_entry const* entry = fi->get_entry(i);
                args.reset();
                args.push_back(r);
                args.append(f->get_arity(), entry->get_args());
                args.push_back(entry->get_result());
                r = array.mk_store(args);
            }
            changed = true;
            t = r;
            trail.push_back(r);
            return true;
        }
    };
    array_cfg cfg(m, cex);
    rewriter_tpl<array_cfg> rw(m, false, cfg);
    expr_ref result(m);
    rw(e, result);
    for (unsigned i = 0; i < 3 && cfg.changed; ++i) {
        cfg.changed = false;
        expr_ref next(m);
        rw(result, next);
        result = next;
    }
    return result;
}
