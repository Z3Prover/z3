/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_model_checker.cpp

Abstract:

    Model checker

Author:

    Leonardo de Moura (leonardo) 2010-12-03.

Revision History:

- to support lambdas/array models:
  binding sk -> (as-array k!0)
  then include definition for k!0 as part of binding.
  Binding instance can be a pointer into m_pinned expressions.

--*/

#include "ast/normal_forms/pull_quant.h"
#include "ast/for_each_expr.h"
#include "ast/occurs.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/has_free_vars.h"
#include "ast/well_sorted.h"
#include "ast/ast_util.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/ast_pp.h"
#include "ast/array_decl_plugin.h"
#include "ast/special_relations_decl_plugin.h"
#include "ast/ast_smt2_pp.h"
#include "smt/smt_model_checker.h"
#include "smt/smt_context.h"
#include "smt/smt_model_finder.h"
#include "model/model_pp.h"
#include <tuple>

namespace smt {

    model_checker::model_checker(ast_manager & m, qi_params const & p, model_finder & mf):
        m(m),
        m_params(p),
        m_autil(m),
        m_qm(nullptr),
        m_context(nullptr),
        m_root2value(nullptr),
        m_model_finder(mf),
        m_max_cexs(1),
        m_iteration_idx(0),
        m_curr_model(nullptr),
        m_fresh_exprs(m),
        m_pinned_exprs(m) {
    }

    model_checker::~model_checker() {
        m_aux_context = nullptr; // delete aux context before fparams
        m_fparams = nullptr;
    }

    quantifier * model_checker::get_flat_quantifier(quantifier * q) {
        return m_model_finder.get_flat_quantifier(q);
    }

    void model_checker::set_qm(quantifier_manager & qm) {
        SASSERT(m_qm == nullptr);
        SASSERT(m_context == nullptr);
        m_qm = &qm;
        m_context = &(m_qm->get_context());
    }

    /**
       \brief Return a term in the context that evaluates to val.
    */
    expr * model_checker::get_term_from_ctx(expr * val) {
        init_value2expr();
        expr * t = nullptr;
        m_value2expr.find(val, t);
        return t;
    }

    expr * model_checker::get_type_compatible_term(expr * val) {
        app* fresh_term;
        if (is_app(val) && to_app(val)->get_num_args() > 0) {
            ptr_buffer<expr> args;
            for (expr* arg : *to_app(val)) 
                args.push_back(get_type_compatible_term(arg));
            fresh_term = m.mk_app(to_app(val)->get_decl(), args.size(), args.data());
        }
        else {
            expr * sk_term = get_term_from_ctx(val);
            if (sk_term != nullptr) 
                return sk_term;

            for (expr* f : m_fresh_exprs) 
                if (f->get_sort() == val->get_sort()) 
                    return f;
            fresh_term = m.mk_fresh_const("sk", val->get_sort());
        }
        m_fresh_exprs.push_back(fresh_term);
        m_context->ensure_internalized(fresh_term);
        return fresh_term;
    }

    void model_checker::init_value2expr() {
        
        if (m_value2expr.empty()) {
            // populate m_value2expr
            for (auto const& kv : *m_root2value) {
                enode * n   = kv.m_key;
                expr  * val = kv.m_value;
                n = n->get_eq_enode_with_min_gen(m_context);
                expr* e = n->get_expr();
                if (!m.is_value(e))
                    m_value2expr.insert(val, e);
            }
        }
    }

    expr_ref model_checker::replace_value_from_ctx(expr * e) {
        init_value2expr();
        struct beta_reducer_cfg : default_rewriter_cfg {
            model_checker& mc;
            beta_reducer_cfg(model_checker& mc):mc(mc) {}
            bool get_subst(expr * e, expr* & t, proof *& pr) {
                t = nullptr; pr = nullptr;
                mc.m_value2expr.find(e, t);
                return t != nullptr;
            }
        };
        struct beta_reducer : public rewriter_tpl<beta_reducer_cfg> {
            beta_reducer_cfg m_cfg;
            beta_reducer(model_checker& m):
                rewriter_tpl<beta_reducer_cfg>(m.m, false, m_cfg), m_cfg(m) {}
        };
        beta_reducer br(*this);
        expr_ref result(m);
        br(e, result);
        return result;
    }

    expr_ref model_checker::replace_model_values(expr * e) {
        struct mv_cfg : default_rewriter_cfg {
            model_checker& mc;
            mv_cfg(model_checker& mc):mc(mc) {}
            bool get_subst(expr * e, expr* & t, proof *& pr) {
                t = nullptr; pr = nullptr;
                if (mc.m.is_model_value(e))
                    t = mc.get_type_compatible_term(e);
                return t != nullptr;
            }
        };
        struct mv_rw : public rewriter_tpl<mv_cfg> {
            mv_cfg m_mv_cfg;
            mv_rw(model_checker& m): rewriter_tpl<mv_cfg>(m.m, false, m_mv_cfg), m_mv_cfg(m) {}
        };
        mv_rw r(*this);
        expr_ref result(m);
        r(e, result);
        return result;
    }

    /**
       \brief Assert in m_aux_context, the constraint

         sk = e_1 OR ... OR sk = e_n

         where {e_1, ..., e_n} is the universe.
     */
    void model_checker::restrict_to_universe(expr * sk, obj_hashtable<expr> const & universe) {
        SASSERT(!universe.empty());
        ptr_buffer<expr> eqs;
        for (expr * e : universe) {
            eqs.push_back(m.mk_eq(sk, e));
        }
        expr_ref fml(m.mk_or(eqs), m);
        m_aux_context->assert_expr(fml);
    }

    /**
       \brief Assert the negation of q after applying the interpretation in m_curr_model to the uninterpreted symbols in q.

       The variables are replaced by skolem constants. These constants are stored in sks.
    */

    bool model_checker::assert_neg_q_m(quantifier * q, expr_ref_vector & sks) {
        expr_ref tmp(m);
        
        TRACE(model_checker, tout << "curr_model:\n"; model_pp(tout, *m_curr_model););

        if (!m_curr_model->eval(q->get_expr(), tmp, true)) {
            return false;
        }
        TRACE(model_checker, tout << "q after applying interpretation:\n" << mk_ismt2_pp(tmp, m) << "\n";);
        ptr_buffer<expr> subst_args;
        unsigned num_decls = q->get_num_decls();
        subst_args.resize(num_decls, nullptr);
        sks.resize(num_decls, nullptr);
        for (unsigned i = 0; i < num_decls; ++i) {
            sort * s  = q->get_decl_sort(num_decls - i - 1);
            expr * sk = m.mk_fresh_const(nullptr, s);
            sks[num_decls - i - 1]        = sk;
            subst_args[num_decls - i - 1] = sk;
            if (m_curr_model->is_finite(s)) {
                restrict_to_universe(sk, m_curr_model->get_known_universe(s));
            }
        }

        var_subst s(m);
        expr_ref sk_body = s(tmp, subst_args.size(), subst_args.data());
        expr_ref r(m);
        r = m.mk_not(sk_body);
        TRACE(model_checker, tout << "mk_neg_q_m:\n" << mk_ismt2_pp(r, m) << "\n";);
        m_aux_context->assert_expr(r);
        return true;
    }

    bool model_checker::add_instance(quantifier * q, model * cex, expr_ref_vector & sks, bool use_inv) {
        if (cex == nullptr || sks.empty()) {
            TRACE(model_checker, tout << "no model is available\n";);
            return false;
        }
        array_util autil(m);
        unsigned num_decls = q->get_num_decls();
        // Remark: sks were created for the flat version of q.
        SASSERT(sks.size() >= num_decls);
        expr_ref_vector bindings(m), alternatives(m), alternatives2(m);
        ptr_vector<func_decl> bases(num_decls, (func_decl*)nullptr);
        expr_ref def(m);
        bindings.resize(num_decls);
        alternatives.resize(num_decls);
        alternatives2.resize(num_decls);
        unsigned max_generation = 0;
        for (unsigned i = 0; i < num_decls; ++i) {
            expr * sk = sks.get(num_decls - i - 1);
            func_decl * sk_d = to_app(sk)->get_decl();
            expr_ref sk_value(cex->get_some_const_interp(sk_d), m);
            if (!sk_value) {
                TRACE(model_checker, tout << "Could not get value for " << sk_d->get_name() << "\n";);
                return false; // get_some_value failed... giving up
            }
            TRACE(model_checker, tout << "Got some value " << sk_value << "\n";);

            if (use_inv) {
                unsigned sk_term_gen = 0;
                expr * sk_term = m_model_finder.get_inv(q, i, sk_value, *cex, sk_term_gen);
                if (sk_term != nullptr) {
                    TRACE(model_checker, tout << "Found inverse " << mk_pp(sk_term, m) << "\n";);
                    // get_inv may return a model value in polymorphic settings;
                    // this is handled downstream by get_type_compatible_term.
                    max_generation = std::max(sk_term_gen, max_generation);
                    sk_value = sk_term;
                }
                else {
                    TRACE(model_checker, tout << "no inverse value for " << sk_value << "\n";);
                    return false;
                }
            }
            else {
                expr * sk_term = get_term_from_ctx(sk_value);
                if (sk_term != nullptr) {
                    TRACE(model_checker, tout << "sk term " << mk_pp(sk_term, m) << "\n");
                    sk_value = sk_term;
                }

            }
            if (contains_model_value(sk_value)) {
                TRACE(model_checker, tout << "type compatible term " << mk_pp(sk_value, m) << "\n");
                sk_value = get_type_compatible_term(sk_value);
            }
            func_decl * f = nullptr;
            expr_ref sk_term(sk_value, m);
            if (!autil.is_as_array(sk_value)) {
                // array values nested in the binding (e.g. inside a datatype constructor)
                expr_ref conv = as_array_to_stores(sk_value, cex);
                if (conv != sk_value) {
                    conv = replace_value_from_ctx(conv);
                    if (contains_model_value(conv))
                        conv = replace_model_values(conv);
                    IF_VERBOSE(10, verbose_stream() << "(smt.mbqi :nested-array-value-as-stores " << q->get_qid() << " " << mk_pp(conv, m) << ")\n");
                    sk_term = conv;
                    sk_value = conv;
                }
            }
            if (autil.is_as_array(sk_value, f) && cex->get_func_interp(f) && cex->get_func_interp(f)->get_interp()) {
                // Besides the lambda built from the interpretation (below), also instantiate with
                // the same modifications applied to an array term of the main context, if any.
                func_decl * base = nullptr;
                expr_ref store_term = mk_store_instance(f, cex, base);

                if (base)
                    bases[num_decls - i - 1] = base;
                if (store_term) {
                    IF_VERBOSE(10, verbose_stream() << "(smt.mbqi :array-store-instance " << q->get_qid() << " " << mk_pp(store_term, m) << ")\n");
                    alternatives[num_decls - i - 1] = store_term;
                }
                expr_ref body(cex->get_func_interp(f)->get_interp(), m);
                unsigned arity = f->get_arity();
                if (arity > 1) {
                    // func_interp::get_interp() refers to argument i as (:var i), whereas the lambda
                    // (lambda ((x_0 S_0) .. (x_{n-1} S_{n-1})) body) built below refers to x_i as
                    // (:var n-1-i): reverse the variable indices (the two coincide for arity 1).
                    expr_ref_vector rev(m);
                    for (unsigned j = 0; j < arity; ++j)
                        rev.push_back(m.mk_var(arity - 1 - j, f->get_domain(j)));
                    var_subst vs(m, false);
                    body = vs(body, rev.size(), rev.data());
                }
                body = replace_value_from_ctx(body);
                if (contains_model_value(body)) {
                    // The array interpretation refers to model values that have no
                    // representative in the main context (e.g. elements of an
                    // uninterpreted sort). Instantiating with any term of the right
                    // sort is sound, so map each such value to a type compatible term
                    // (an existing term when available, a fresh constant otherwise)
                    // instead of giving up on the instance.
                    body = replace_model_values(body);
                    IF_VERBOSE(10, verbose_stream() << "(smt.mbqi :array-interp-model-values-replaced " << q->get_qid() << " " << mk_pp(body, m) << ")\n");
                }
                ptr_vector<sort> sorts(f->get_arity(), f->get_domain());
                svector<symbol> names;
                for (unsigned i = 0; i < f->get_arity(); ++i) 
                    names.push_back(symbol(i));
                body = m.mk_lambda(sorts.size(), sorts.data(), names.data(), body);
                sk_term = body;
            }
            bindings.set(num_decls - i - 1, sk_term);
        }

        TRACE(model_checker, tout << q->get_qid() << " found (use_inv: " << use_inv << ") new instance: " << bindings << "\n");
        max_generation = std::max(m_qm->get_generation(q), max_generation);
        add_instance(q, bindings, max_generation);
        for (unsigned i = 0; i < num_decls; ++i) {
            if (alternatives.get(i)) {
                expr_ref_vector alt_bindings(bindings);
                alt_bindings[i] = alternatives.get(i);
                add_instance(q, alt_bindings, max_generation);
            }
            if (alternatives2.get(i)) {
                expr_ref_vector alt_bindings(bindings);
                alt_bindings[i] = alternatives2.get(i);
                add_instance(q, alt_bindings, max_generation);
            }
        }
        // Array variables: the lambdas of the quantifier that mention the variable (e.g. a
        // canonicalisation lambda (x) -> ite(guard(x), f[x], default)), closed by the bindings of
        // the other variables and with the occurrences of f replaced by a ground value of the
        // quantifier, are natural candidates for f: they are the functions the quantifier itself
        // considers, constant on their domain.
        bool q_has_lambda = false;
        for (expr * t : subterms::all(expr_ref(q->get_expr(), m)))
            if (is_lambda(t)) { q_has_lambda = true; break; }
        if (q_has_lambda) {
            expr_ref_vector vals(m);
            for (unsigned i = 0; i < num_decls; ++i) {
                sort * asrt = bindings.get(i)->get_sort();
                if (!autil.is_array(asrt))
                    continue;
                sort * vsrt = get_array_range(asrt);
                vals.reset();
                obj_hashtable<expr> seen;
                for (expr * t : subterms::all(expr_ref(q->get_expr(), m))) {
                    if (vals.size() >= 4)
                        break;
                    if (is_app(t) && is_ground(t) && t->get_sort() == vsrt && !seen.contains(t)) {
                        seen.insert(t);
                        vals.push_back(t);
                    }
                }
                if (vals.empty())
                    continue;
                // instantiate the body with a placeholder for position i and collect the closed
                // lambdas that apply the placeholder
                expr_ref placeholder(m.mk_fresh_const("mbqi_f", asrt), m);
                expr_ref_vector subst(bindings);
                subst[i] = placeholder;
                expr_ref body_inst = instantiate(m, q, subst.data());
                unsigned num_lambdas = 0;
                for (expr * t : subterms::all(body_inst)) {
                    if (!is_lambda(t))
                        continue;
                    if (t->get_sort() != asrt || has_free_vars(t) || num_lambdas >= 2)
                        continue;
                    ptr_vector<expr> sels;
                    for (expr * u : subterms::all(expr_ref(to_quantifier(t)->get_expr(), m)))
                        if (autil.is_select(u) && to_app(u)->get_arg(0) == placeholder)
                            sels.push_back(u);
                    if (sels.empty())
                        continue;
                    ++num_lambdas;
                    for (expr * v : vals) {
                        // replace every select(placeholder, ...) in the lambda by v
                        struct sel_cfg : default_rewriter_cfg {
                            array_util & a; expr * ph; expr * v;
                            sel_cfg(array_util & a, expr * ph, expr * v): a(a), ph(ph), v(v) {}
                            br_status reduce_app(func_decl * f, unsigned n, expr * const * args, expr_ref & result, proof_ref & pr) {
                                if (a.is_select(f) && n > 0 && args[0] == ph) { result = v; return BR_DONE; }
                                return BR_FAILED;
                            }
                        };
                        sel_cfg cfg(autil, placeholder, v);
                        rewriter_tpl<sel_cfg> rw(m, false, cfg);
                        expr_ref cand(m);
                        rw(t, cand);
                        if (!is_lambda(cand) || occurs(placeholder, to_quantifier(cand)->get_expr()))
                            continue;
                        expr_ref_vector alt_bindings(bindings);
                        alt_bindings[i] = cand;
                        IF_VERBOSE(10, verbose_stream() << "(smt.mbqi :lambda-instance " << q->get_qid() << " " << mk_pp(cand, m) << ")\n");
                        add_instance(q, alt_bindings, max_generation);
                    }
                }
            }
        }
        // Datatype variables whose binding carries an array inside a constructor (e.g. a boxed
        // function mk(f)): also instantiate with the array replaced by the constant functions
        // (const v) for the ground values v of the quantifier, the analogue for boxed functions
        // of the constant-function instances above.
        {
            datatype::util dtu(m);
            for (unsigned i = 0; i < num_decls; ++i) {
                expr * b = bindings.get(i);
                if (!dtu.is_datatype(b->get_sort()) || !is_app(b) || !dtu.is_constructor(to_app(b)))
                    continue;
                app * cons = to_app(b);
                for (unsigned k = 0; k < cons->get_num_args(); ++k) {
                    expr * arg = cons->get_arg(k);
                    sort * asrt = arg->get_sort();
                    if (!autil.is_array(asrt))
                        continue;
                    sort * vsrt = get_array_range(asrt);
                    expr_ref_vector vals(m);
                    obj_hashtable<expr> seen;
                    for (expr * t : subterms::all(expr_ref(q->get_expr(), m))) {
                        if (vals.size() >= 4)
                            break;
                        if (is_app(t) && is_ground(t) && t->get_sort() == vsrt && !seen.contains(t)) {
                            seen.insert(t);
                            vals.push_back(t);
                        }
                    }
                    for (expr * v : vals) {
                        expr_ref_vector cargs(m);
                        for (unsigned j = 0; j < cons->get_num_args(); ++j)
                            cargs.push_back(j == k ? autil.mk_const_array(asrt, v) : cons->get_arg(j));
                        expr_ref alt(m.mk_app(cons->get_decl(), cargs.size(), cargs.data()), m);
                        expr_ref_vector alt_bindings(bindings);
                        alt_bindings[i] = alt;
                        IF_VERBOSE(10, verbose_stream() << "(smt.mbqi :boxed-const-instance " << q->get_qid() << " " << mk_pp(alt, m) << ")\n");
                        add_instance(q, alt_bindings, max_generation);
                    }
                }
            }
        }
        // Array variables constrained pointwise by a canonicity guard
        //    forall x. ite(G(x), P(f[x]), f[x] = d)     (or  (not G(x)) => f[x] = d)
        // are instantiated with the guarded constant functions (lambda (x) (ite G(x) v d)) for
        // the ground values v of the quantifier: the shape such a quantifier admits.
        for (unsigned i = 0; i < num_decls; ++i) {
            sort * asrt = bindings.get(i)->get_sort();
            if (!autil.is_array(asrt) || get_array_arity(asrt) != 1)
                continue;
            // only when the problem offers no array of that sort to modify (otherwise the
            // store instances above are the better candidates)
            bool has_ctx_array = false;
            for (unsigned c = 0; c < m_curr_model->get_num_constants() && !has_ctx_array; ++c)
                if (m_curr_model->get_constant(c)->get_range() == asrt && !m_curr_model->get_constant(c)->is_skolem())
                    has_ctx_array = true;
            if (has_ctx_array)
                continue;
            sort * vsrt = get_array_range(asrt);
            expr_ref placeholder(m.mk_fresh_const("mbqi_g", asrt), m);
            expr_ref_vector subst(bindings);
            subst[i] = placeholder;
            expr_ref body_inst = instantiate(m, q, subst.data());
            expr_ref_vector vals(m);
            obj_hashtable<expr> seen;
            for (expr * t : subterms::all(expr_ref(q->get_expr(), m))) {
                if (vals.size() >= 4) break;
                if (is_app(t) && is_ground(t) && t->get_sort() == vsrt && !seen.contains(t)) { seen.insert(t); vals.push_back(t); }
            }
            // also ground terms of the codomain sort present in the context (e.g. the inhabitant
            // coerce(unit) of an uninterpreted codomain sort), skipping invented elements and skolems
            for (enode * n : m_context->enodes()) {
                if (vals.size() >= 6) break;
                expr * e = n->get_expr();
                if (e->get_sort() != vsrt || !is_app(e) || !is_ground(e) || seen.contains(e))
                    continue;
                bool clean = true;
                for (expr * u : subterms::all(expr_ref(e, m)))
                    if (is_app(u) && (to_app(u)->get_decl()->is_skolem() || to_app(u)->get_decl()->get_name().str().compare(0, 5, "elem!") == 0 || to_app(u)->get_decl()->get_name().str().compare(0, 2, "k!") == 0)) { clean = false; break; }
                if (!clean) continue;
                seen.insert(e); vals.push_back(e);
            }
            if (vals.empty())
                continue;
            unsigned num_found = 0;
            sort * dom = get_array_domain(asrt, 0);
            for (expr * t : subterms::all(body_inst)) {
                if (num_found >= 2)
                    break;
                // The guard shape appears either under the nested quantifier (positive occurrence)
                // or, after skolemisation, applied to a skolem term of the index sort.
                expr * ib = t;
                bool under_forall = false;
                if (is_forall(t)) {
                    quantifier * inner = to_quantifier(t);
                    if (inner->get_num_decls() != 1 || inner->get_decl_sort(0) != dom)
                        continue;
                    ib = inner->get_expr();
                    under_forall = true;
                }
                else if (!m.is_ite(t) && !m.is_or(t) && !m.is_implies(t))
                    continue;
                expr * G = nullptr, * eq = nullptr, * c = nullptr, * a = nullptr, * b = nullptr;
                if (m.is_ite(ib, c, a, b)) { G = c; eq = b; }
                else if (m.is_implies(ib, c, a) && m.is_not(c, c)) { G = c; eq = a; }
                else if (m.is_or(ib) && to_app(ib)->get_num_args() == 2) {
                    expr * o0 = to_app(ib)->get_arg(0), * o1 = to_app(ib)->get_arg(1);
                    if (m.is_eq(o1) && m.is_not(o0, c)) { G = c; eq = o1; }
                    else if (m.is_eq(o0) && m.is_not(o1, c)) { G = c; eq = o0; }
                    else if (m.is_eq(o1)) { G = o0; eq = o1; }
                    else if (m.is_eq(o0)) { G = o1; eq = o0; }
                }
                expr * lhs = nullptr, * rhs = nullptr, * d = nullptr, * idx = nullptr;
                if (!G || !eq || !m.is_eq(eq, lhs, rhs))
                    continue;
                if (autil.is_select(lhs) && to_app(lhs)->get_arg(0) == placeholder && to_app(lhs)->get_num_args() == 2) { d = rhs; idx = to_app(lhs)->get_arg(1); }
                else if (autil.is_select(rhs) && to_app(rhs)->get_arg(0) == placeholder && to_app(rhs)->get_num_args() == 2) { d = lhs; idx = to_app(rhs)->get_arg(1); }
                if (!d || occurs(placeholder, d) || !is_ground(d))
                    continue;
                if (under_forall ? !is_var(idx) : !is_ground(idx))
                    continue;
                // guard as a function of the index: G[idx := x]; the substitution of a bound
                // variable is only valid when the guard contains no binders of its own
                expr_ref Gx(G, m);
                bool g_has_binders = false;
                for (expr * u : subterms::all(expr_ref(G, m)))
                    if (is_quantifier(u)) { g_has_binders = true; break; }
                if (g_has_binders)
                    continue;
                if (!under_forall) {
                    expr_safe_replace rep(m);
                    rep.insert(idx, m.mk_var(0, dom));
                    rep(G, Gx);
                }
                if (occurs(placeholder, Gx))
                    continue;
                ++num_found;
                // bindings that are fresh elements invented by the model finder (elem!k) carry no
                // information; use a constant of the context of that sort instead when there is one
                expr_ref_vector fixed(bindings);
                expr_ref repaired_G(Gx, m);
                {
                    expr_safe_replace rep(m);
                    bool any = false;
                    for (unsigned j = 0; j < num_decls; ++j) {
                        expr * bj = bindings.get(j);
                        if (!is_app(bj) || to_app(bj)->get_num_args() != 0 || !m.is_uninterp(bj->get_sort()))
                            continue;
                        std::string bn = to_app(bj)->get_decl()->get_name().str();
                        if (bn.compare(0, 5, "elem!") != 0)
                            continue;
                        // any ground term of the context of that sort that is not itself an
                        // invented element or skolem (e.g. coerce(unit))
                        for (enode * n : m_context->enodes()) {
                            expr * e = n->get_expr();
                            if (e->get_sort() != bj->get_sort() || !is_app(e) || !is_ground(e))
                                continue;
                            func_decl * fd = to_app(e)->get_decl();
                            std::string fn = fd->get_name().str();
                            if (fd->is_skolem() || fn.compare(0, 5, "elem!") != 0 == false || fn.compare(0, 3, "sk!") == 0 || fn.compare(0, 2, "k!") == 0)
                                continue;
                            bool clean = true;
                            for (expr * u : subterms::all(expr_ref(e, m)))
                                if (is_app(u) && (to_app(u)->get_decl()->is_skolem() || to_app(u)->get_decl()->get_name().str().compare(0, 5, "elem!") == 0)) { clean = false; break; }
                            if (!clean)
                                continue;
                            expr_ref ct(e, m);
                            fixed[j] = ct;
                            rep.insert(bj, ct);
                            any = true;
                            break;
                        }
                    }
                    if (any)
                        rep(Gx, repaired_G);
                }
                bool has_invented = false;
                for (unsigned j = 0; j < num_decls && !has_invented; ++j) {
                    expr * bj = fixed.get(j);
                    if (is_app(bj) && to_app(bj)->get_num_args() == 0 && to_app(bj)->get_decl()->get_name().str().compare(0, 5, "elem!") == 0)
                        has_invented = true;
                }
                if (has_invented)
                    continue;
                for (expr * v : vals) {
                    if (v == d) continue;
                    expr_ref lam_body(m.mk_ite(repaired_G, v, d), m);
                    symbol nm("x");
                    expr_ref cand(m.mk_lambda(1, &dom, &nm, lam_body), m);
                    if (has_free_vars(cand))
                        continue;
                    expr_ref_vector alt_bindings(fixed);
                    alt_bindings[i] = cand;
                    IF_VERBOSE(10, verbose_stream() << "(smt.mbqi :guarded-lambda-instance " << q->get_qid() << " " << mk_pp(cand, m) << ")\n");
                    add_instance(q, alt_bindings, max_generation);
                }
            }
        }
        // Array variables: also the context array modified at the points the instance binds
        // the other variables to, with the ground values of the quantifier. In a model the
        // interpretation of the context array is arbitrary away from the instantiated points,
        // so a modification refuting the quantifier in the problem need not refute it in the
        // model; these instances are the natural candidates regardless.
        for (unsigned i = 0; i < num_decls; ++i) {
            if (!bases[i])
                continue;
            sort * asrt = bases[i]->get_range();
            if (get_array_arity(asrt) != 1)
                continue;
            sort * isrt = get_array_domain(asrt, 0);
            sort * vsrt = get_array_range(asrt);
            expr_ref_vector vals(m);
            obj_hashtable<expr> seen;
            for (expr * t : subterms::all(expr_ref(q->get_expr(), m))) {
                if (vals.size() >= 4)
                    break;
                if (is_app(t) && is_ground(t) && t->get_sort() == vsrt && !seen.contains(t)) {
                    seen.insert(t);
                    vals.push_back(t);
                }
            }
            expr_ref base(m.mk_const(bases[i]), m);
            for (unsigned j = 0; j < num_decls; ++j) {
                if (j == i || bindings.get(j)->get_sort() != isrt)
                    continue;
                for (expr * v : vals) {
                    expr * args[3] = { base, bindings.get(j), v };
                    expr_ref_vector alt_bindings(bindings);
                    alt_bindings[i] = autil.mk_store(3, args);
                    add_instance(q, alt_bindings, max_generation);
                }
            }
        }
        return true;
    }

    /**
       \brief Given the array value as-array[f] of a skolem in the counterexample model cex,
       build the term store(A, i1, v1, ..., in, vn) where A is an array constant of the main
       context with the same sort and (i_k, v_k) are the entries of the interpretation of f
       on which A (in the current model) differs. The term agrees with the counterexample on
       all points the counterexample cares about (its entries); outside of them it follows A.
       Unlike the lambda built from the interpretation it is expressed with terms of the main
       context, so the array theory can relate it to A by extensionality (e.g. the instance
       "modify the known function at one point") and no lambda is introduced as argument of
       uninterpreted (skolem) functions, on which the array theory is incomplete.
       Returns null when there is no such A.
    */
    expr_ref model_checker::mk_store_instance(func_decl * f, model * cex, func_decl *& base) {
        expr_ref result(m);
        base = nullptr;
        func_interp * fi = cex->get_func_interp(f);
        if (!fi || f->get_arity() == 0)
            return result;
        array_util autil(m);
        sort * arr_sort = autil.mk_array_sort(f->get_arity(), f->get_domain(), f->get_range());
        func_decl * best = nullptr;
        unsigned best_cost = UINT_MAX;
        unsigned num_consts = m_curr_model->get_num_constants();
        for (unsigned i = 0; i < num_consts; ++i) {
            func_decl * c = m_curr_model->get_constant(i);
            if (c->get_range() != arr_sort || c->is_skolem())
                continue;
            expr * val = m_curr_model->get_const_interp(c);
            func_decl * g = nullptr;
            func_interp * fa = (val && autil.is_as_array(val, g)) ? m_curr_model->get_func_interp(g) : nullptr;
            unsigned cost = 0;
            for (unsigned k = 0; k < fi->num_entries(); ++k) {
                func_entry const * e = fi->get_entry(k);
                func_entry * ea = fa ? fa->get_entry(e->get_args()) : nullptr;
                if (!ea || ea->get_result() != e->get_result())
                    ++cost;
            }
            if (cost < best_cost) {
                best = c;
                best_cost = cost;
            }
        }
        if (!best)
            return result;
        base = best;
        result = m.mk_const(best);
        expr * val = m_curr_model->get_const_interp(best);
        func_decl * g = nullptr;
        func_interp * fa = (val && autil.is_as_array(val, g)) ? m_curr_model->get_func_interp(g) : nullptr;
        unsigned arity = f->get_arity();
        expr_ref_vector args(m);
        for (unsigned k = 0; k < fi->num_entries(); ++k) {
            func_entry const * e = fi->get_entry(k);
            func_entry * ea = fa ? fa->get_entry(e->get_args()) : nullptr;
            if (ea && ea->get_result() == e->get_result())
                continue;
            args.reset();
            args.push_back(result);
            args.append(arity, e->get_args());
            args.push_back(e->get_result());
            result = autil.mk_store(args);
        }
        result = replace_value_from_ctx(result);
        if (contains_model_value(result))
            result = replace_model_values(result);
        return result;
    }

    /**
       \brief Replace every array model value as-array[f] occurring in e (also nested inside
       datatype values) whose interpretation in cex is a finite table with a default by the term
       store(...(store (const default) i1 v1)... in vn). Unlike a lambda, such a term is fully
       supported by the array theory wherever it occurs (e.g. as argument of a constructor or of an
       uninterpreted function), so the instance does not make the theory give up on the model.
       Model values in indices and values are mapped to terms of the context as usual.
       Returns e itself when nothing was converted.
    */
    expr_ref model_checker::as_array_to_stores(expr * e, model * cex) {
        struct aa_cfg : default_rewriter_cfg {
            model_checker & mc; model * cex; array_util autil; bool changed = false; bool failed = false;
            aa_cfg(model_checker & mc, model * cex): mc(mc), cex(cex), autil(mc.m) {}
            bool get_subst(expr * e, expr* & t, proof *& pr) {
                t = nullptr; pr = nullptr;
                func_decl * f = nullptr;
                if (!autil.is_as_array(e, f))
                    return false;
                func_interp * fi = cex->get_func_interp(f);
                if (!fi || !fi->get_else()) { failed = true; return false; }
                sort * asrt = e->get_sort();
                unsigned arity = f->get_arity();
                expr_ref r(autil.mk_const_array(asrt, fi->get_else()), mc.m);
                expr_ref_vector args(mc.m);
                for (unsigned i = 0; i < fi->num_entries(); ++i) {
                    func_entry const * en = fi->get_entry(i);
                    args.reset();
                    args.push_back(r);
                    args.append(arity, en->get_args());
                    args.push_back(en->get_result());
                    r = autil.mk_store(args);
                }
                changed = true;
                t = r;
                mc.m_pinned_exprs.push_back(r);
                return true;
            }
        };
        aa_cfg cfg(*this, cex);
        rewriter_tpl<aa_cfg> rw(m, false, cfg);
        expr_ref result(m);
        rw(e, result);
        // nested as-array values inside the stores are converted by the traversal of the
        // rewriter; repeat while something changes (values of entries may be arrays too)
        for (unsigned k = 0; k < 3 && cfg.changed; ++k) {
            cfg.changed = false;
            expr_ref r2(m);
            rw(result, r2);
            result = r2;
        }
        return result;
    }

    // well-sortedness check that does not print warnings (is_well_sorted does)
    static bool is_well_sorted_quiet(ast_manager & m, expr * e) {
        ptr_vector<expr> todo;
        ast_mark visited;
        todo.push_back(e);
        while (!todo.empty()) {
            expr * t = todo.back(); todo.pop_back();
            if (visited.is_marked(t)) continue;
            visited.mark(t, true);
            if (is_quantifier(t)) { todo.push_back(to_quantifier(t)->get_expr()); continue; }
            if (!is_app(t)) continue;
            app * a = to_app(t);
            func_decl * d = a->get_decl();
            unsigned n = a->get_num_args();
            if (d->get_arity() == n) {
                for (unsigned i = 0; i < n; ++i)
                    if (a->get_arg(i)->get_sort() != d->get_domain(i))
                        return false;
            }
            else if (d->is_associative() || m.is_eq(d) || m.is_distinct(d) || d->get_arity() == 0) {
                for (unsigned i = 1; i < n; ++i)
                    if ((m.is_eq(d) || m.is_distinct(d)) && a->get_arg(i)->get_sort() != a->get_arg(0)->get_sort())
                        return false;
            }
            for (expr * arg : *a) todo.push_back(arg);
        }
        return true;
    }

    void model_checker::add_instance(quantifier* q, expr_ref_vector const& bindings, unsigned max_generation) {
        SASSERT(q->get_num_decls() == bindings.size());
        // Instances built from counterexample values and context terms must be well formed:
        // one closed binding of the declared sort per variable.
        if (q->get_num_decls() != bindings.size()) {
            IF_VERBOSE(10, verbose_stream() << "(smt.mbqi :skip-instance " << q->get_qid() << " :reason arity " << bindings.size() << " vs " << q->get_num_decls() << ")\n");
            return;
        }
        for (unsigned i = 0; i < bindings.size(); ++i) {
            // bindings[i] has the sort of the i-th declared variable (see assert_neg_q_m / add_instance)
            expr* b = bindings.get(i);
            sort* expected = q->get_decl_sort(i);
            if (!b || b->get_sort() != expected || has_free_vars(b) || !is_well_sorted_quiet(m, b)) {
                IF_VERBOSE(10, verbose_stream() << "(smt.mbqi :skip-instance " << q->get_qid() << " :var " << i << " :reason " << (!b ? "null" : b->get_sort() != expected ? "sort" : has_free_vars(b) ? "free-vars" : "ill-sorted") << " "; if (b) verbose_stream() << mk_pp(b, m); verbose_stream() << ")\n");
                return;
            }
        }
        IF_VERBOSE(10, verbose_stream() << "(smt.mbqi :instance " << q->get_qid(); for (expr* b : bindings) verbose_stream() << " [" << mk_pp(b, m) << "]"; verbose_stream() << ")\n");
        unsigned offset = m_pinned_exprs.size();
        m_pinned_exprs.append(bindings);
        m_pinned_exprs.push_back(q);
        m_new_instances.push_back(instance(q, offset, max_generation));
    }

    void model_checker::operator()(expr *n) {
        if (m.is_model_value(n) /*|| m_autil.is_as_array(n)*/) {
            throw is_model_value();
        }
    }

    bool model_checker::contains_model_value(expr* n) {
        if (m.is_model_value(n) /*|| m_autil.is_as_array(n)*/) {
            return true;
        }
        if (is_app(n) && to_app(n)->get_num_args() == 0) {
            return false;
        }
        m_visited.reset();
        try {
            for_each_expr(*this, m_visited, n);
        }
        catch (const is_model_value &) {
            return true;
        }
        return false;
    }

    bool model_checker::add_blocking_clause(model * cex, expr_ref_vector & sks) {
        SASSERT(cex != nullptr);
        expr_ref_buffer diseqs(m);
        for (expr * sk : sks) {
            func_decl * sk_d = to_app(sk)->get_decl();
            expr_ref sk_value(cex->get_some_const_interp(sk_d), m);
            if (!sk_value) {
                TRACE(model_checker, tout << "no constant interpretation for " << mk_pp(sk, m) << "\n";);
                return false; // get_some_value failed... aborting add_blocking_clause
            }
            diseqs.push_back(m.mk_not(m.mk_eq(sk, sk_value)));
        }
        expr_ref blocking_clause(m);
        blocking_clause = m.mk_or(diseqs);
        TRACE(model_checker, tout << "blocking clause:\n" << mk_ismt2_pp(blocking_clause, m) << "\n";);
        m_aux_context->assert_expr(blocking_clause);
        return true;
    }

    struct scoped_ctx_push {
        context* c;
        scoped_ctx_push(context* c): c(c) { c->push(); }
        ~scoped_ctx_push() { 
            try {
                c->pop(1);
            }
            catch (...) {
                ;
            }
        }
    };

    /**
       \brief Return true if q is satisfied by m_curr_model.
    */

    bool model_checker::check(quantifier * q) {
        SASSERT(!m_aux_context->relevancy());
        scoped_ctx_push _push(m_aux_context.get());

        quantifier * flat_q = get_flat_quantifier(q);
        TRACE(model_checker, tout << "model checking:\n" << expr_ref(flat_q->get_expr(), m) << "\n";);
        expr_ref_vector sks(m);

        IF_VERBOSE(10, verbose_stream() << "(smt.mbqi :check-stage neg-q " << q->get_qid() << ")\n";);
        if (!assert_neg_q_m(flat_q, sks))
            return false;
        IF_VERBOSE(10, verbose_stream() << "(smt.mbqi :check-stage complete-check " << q->get_qid() << ")\n";);
        TRACE(model_checker, tout << "skolems:\n" << sks << "\n";);

        flet<bool> l1(m_aux_context->get_fparams().m_array_fake_support, true);
        flet<bool> l2(m_aux_context->get_fparams().m_preprocess, true);
        lbool r = m_aux_context->check();
        
        TRACE(model_checker, tout << "[complete] model-checker result: " << to_sat_str(r) << "\n";);
        if (r != l_true) {
            return is_safe_for_mbqi(q) && r == l_false; // quantifier is satisfied by m_curr_model
        }

        model_ref complete_cex;
        m_aux_context->get_model(complete_cex);

        unsigned num_new_instances = 0;

        auto restricted_search = [&]() {
            while (true) {
                flet<bool> l1(m_aux_context->get_fparams().m_array_fake_support, true);
                flet<bool> l2(m_aux_context->get_fparams().m_preprocess, true);
                lbool r = m_aux_context->check();
                TRACE(model_checker, tout << "[restricted] model-checker (" << (num_new_instances+1) << ") result: " << to_sat_str(r) << "\n";);
                if (r != l_true)
                    break;
                model_ref cex;
                m_aux_context->get_model(cex);
                
                if (!add_instance(q, cex.get(), sks, true)) {
                    break;
                }
                num_new_instances++;
                if (num_new_instances >= m_max_cexs || !add_blocking_clause(cex.get(), sks)) {
                    TRACE(model_checker, tout << "Add blocking clause failed new-instances: " << num_new_instances << " max-cex: " << m_max_cexs << "\n";);
                    // add_blocking_clause failed... stop the search for new counter-examples...
                    break;
                }
            }
        };

        IF_VERBOSE(10, verbose_stream() << "(smt.mbqi :check-stage restricted " << q->get_qid() << ")\n";);
        // try to find new instances using instantiation sets.
        {
            scoped_ctx_push _push_inst_sets(m_aux_context.get());
            m_model_finder.restrict_sks_to_inst_set(m_aux_context.get(), q, sks);
            restricted_search();
        }

        if (num_new_instances == 0) {
            // no counterexample within the instantiation sets: try array variables as finite
            // modifications store(A, i, v) of the arrays of their instantiation sets. Instances
            // found here are added in addition to the complete counterexample below.
            scoped_ctx_push _push_stores(m_aux_context.get());
            if (m_model_finder.restrict_sks_to_store_candidates(m_aux_context.get(), q, sks)) 
                restricted_search();
            // failed to create instances when restricting to inst sets... then use result of the complete model check
            TRACE(model_checker, tout << "using complete_cex result:\n"; model_pp(tout, *complete_cex););
            add_instance(q, complete_cex.get(), sks, false);
        }

        return false;
    }

    bool model_checker::is_safe_for_mbqi(quantifier * q) const {
        special_relations_util sp(m);
        if (!sp.has_special_relation())
            return true;
        ast_fast_mark1 visited;
        struct proc {
            special_relations_util& sp;
            bool found = false;
            proc(special_relations_util& sp):sp(sp) {}
            void operator()(app* f) {
                found |= sp.is_special_relation(f);
            }
            void operator()(expr* e) {}
        };
        proc p(sp);
        quick_for_each_expr(p, visited, q);
        return !p.found;
    }


    void model_checker::init_aux_context() {
        if (!m_fparams) {
            m_fparams = alloc(smt_params, m_context->get_fparams());
            m_fparams->m_relevancy_lvl = 0; // no relevancy since the model checking problems are quantifier free
            m_fparams->m_mbqi_instances_after_giveup = false; // the auxiliary context checks candidate models only
            m_fparams->m_case_split_strategy = CS_ACTIVITY; // avoid warning messages about smt.case_split >= 3.
            m_fparams->m_axioms2files = false;
            m_fparams->m_lemmas2console = false;
            m_fparams->m_proof_log = symbol::null;
        }
        if (!m_aux_context) {
            symbol logic;
            params_ref p;
            p.set_bool("solver.axioms2files", false);
            p.set_bool("solver.lemmas2console", false);
            p.set_sym("solver.proof.log", symbol::null);
            m_aux_context = m_context->mk_fresh(&logic, m_fparams.get(), p);
        }
    }

    bool model_checker::check(proto_model * md, obj_map<enode, app *> const & root2value) {
        SASSERT(md != nullptr);

        m_root2value = &root2value;

        if (m_qm->num_quantifiers() == 0)
            return true;

        if (m_iteration_idx >= m_params.m_mbqi_max_iterations) {
            IF_VERBOSE(1, verbose_stream() << "(smt.mbqi \"max instantiations " << m_iteration_idx << " reached\")\n";);
            m_context->set_reason_unknown("max mbqi instantiations reached");
            return false;
        }

        m_curr_model = md;
        m_value2expr.reset();

        TRACE(model_checker, tout << "MODEL_CHECKER INVOKED\n";
        tout << "model:\n"; model_pp(tout, *m_curr_model););
	
        md->compress();

        TRACE(model_checker, tout << "MODEL_CHECKER INVOKED\n";
              tout << "model:\n"; model_pp(tout, *m_curr_model););
        if (m_params.m_mbqi_trace) {
            verbose_stream() << "(smt.mbqi \"started\")\n";
        }

        init_aux_context();

        bool found_relevant = false;
        unsigned num_failures = 0;

        check_quantifiers(found_relevant, num_failures);

        if (found_relevant)
            m_iteration_idx++;

        TRACE(model_checker, tout << "model after check:\n"; model_pp(tout, *md););
        TRACE(model_checker, tout << "model checker result: " << (num_failures == 0) << "\n";);
        m_max_cexs += m_params.m_mbqi_max_cexs;

        if (num_failures == 0 && !m_context->validate_model()) {
            num_failures = 1;
            // this time force expanding recursive function definitions
            // that are not forced true in the current model.
            check_quantifiers(found_relevant, num_failures);
        }
        if (num_failures == 0)
            m_curr_model->cleanup();
        if (m_params.m_mbqi_trace) {
            if (num_failures == 0)
                verbose_stream() << "(smt.mbqi :succeeded true)\n";
            else
                verbose_stream() << "(smt.mbqi :num-failures " << num_failures << ")\n";
        }
        return num_failures == 0;
    }

    //
    // (repeated from defined_names.cpp)
    // NB. The pattern for lambdas is incomplete.
    // consider store(a, i, v) == \lambda j . if i = j then v else a[j]
    // the instantiation rules for store(a, i, v) are:
    //     sotre(a, i, v)[j] = if i = j then v else a[j] with patterns {a[j], store(a, i, v)} { store(a, i, v)[j] }
    // The first pattern is not included.
    // TBD use a model-based scheme for extracting instantiations instead of
    // using multi-patterns.
    //

    void model_checker::check_quantifiers(bool& found_relevant, unsigned& num_failures) {
        for (quantifier * q : *m_qm) {
            if (!(m_qm->mbqi_enabled(q) &&
                  m_context->is_relevant(q) &&
                  m_context->get_assignment(q) == l_true)) {
                if (!m_qm->mbqi_enabled(q))
                    ++num_failures;
                continue;
            }

            TRACE(model_checker,
                  tout << "Check: " << mk_pp(q, m) << "\n";
                  tout << m_context->get_assignment(q) << "\n";);

            if (m_params.m_mbqi_trace && q->get_qid() != symbol::null) {
                IF_VERBOSE(1, verbose_stream() << "(smt.mbqi :checking " << q->get_qid() << ")\n");
            }
            found_relevant = true;
            if (!check(q)) {
                if (m_params.m_mbqi_trace || get_verbosity_level() >= 5) {
                    IF_VERBOSE(0, verbose_stream() << "(smt.mbqi :failed " << q->get_qid() << ")\n");
                }
                TRACE(model_checker, tout << "checking quantifier " << mk_pp(q, m) << " failed\n";);
                num_failures++;
            }
        }
    }

    void model_checker::init_search_eh() {
        m_max_cexs = m_params.m_mbqi_max_cexs;
        m_iteration_idx = 0;
    }

    void model_checker::restart_eh() {
        IF_VERBOSE(100, if (has_new_instances()) verbose_stream() << "(smt.mbqi \"instantiating new instances...\")\n";);
        assert_new_instances();
        reset_new_instances();
    }

    bool model_checker::has_new_instances() {
        TRACE(model_checker, tout << "instances: " << m_new_instances.size() << "\n";);
        return !m_new_instances.empty();
    }

    void model_checker::reset_new_instances() {
        m_pinned_exprs.reset();
        m_new_instances.reset();
    }

    void model_checker::reset() {
        reset_new_instances();
    }

    void model_checker::assert_new_instances() {
        TRACE(model_checker_bug_detail, tout << "assert_new_instances, inconsistent: " << m_context->inconsistent() << "\n";);
        ptr_buffer<enode> bindings;
        vector<std::tuple<enode *, enode *>> dummy;
        for (instance const& inst : m_new_instances) {
            quantifier * q  = inst.m_q;
            if (m_context->b_internalized(q)) {
                bindings.reset();
                unsigned num_decls = q->get_num_decls();
                unsigned gen       = inst.m_generation;
                unsigned offset    = inst.m_bindings_offset;
                for (unsigned i = 0; i < num_decls; ++i) {
                    expr * b = m_pinned_exprs.get(offset + i);
                    if (!m_context->e_internalized(b)) {
                        TRACE(model_checker, tout << "internalizing b:\n" << mk_pp(b, m) << "\n";);
                        m_context->internalize(b, false, gen);
                    }
                    bindings.push_back(m_context->get_enode(b));
                }

                TRACE(model_checker_bug_detail, tout << "instantiating... q:\n" << mk_pp(q, m) << "\n";
                      tout << "inconsistent: " << m_context->inconsistent() << "\n";
                      tout << "bindings:\n" << expr_ref_vector(m, num_decls, m_pinned_exprs.data() + offset) << "\n";
                          );
                m_context->add_instance(q, nullptr, num_decls, bindings.data(), gen, gen, gen, dummy, true /* model-based */);
                TRACE(model_checker_bug_detail, tout << "after instantiating, inconsistent: " << m_context->inconsistent() << "\n";);
            }
        }
    }

}
