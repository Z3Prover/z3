/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_antiunify.cpp

Abstract:

  Antiunification utilities

Author:

    Bernhard Gleiss
    Arie Gurfinkel

Revision History:

--*/

#include"muz/spacer/spacer_antiunify.h"
#include"ast/ast.h"
#include"ast/rewriter/rewriter.h"
#include"ast/rewriter/rewriter_def.h"
#include"ast/arith_decl_plugin.h"
#include"ast/ast_util.h"
#include"ast/expr_abstract.h"

namespace spacer {


// Abstracts numeric values by variables
struct var_abs_rewriter : public default_rewriter_cfg {
    ast_manager &m;
    arith_util m_util;
    ast_mark m_seen;
    ast_mark m_has_num;
    unsigned m_var_index;
    expr_ref_vector m_pinned;
    obj_map<expr, expr*>& m_substitution;
    ptr_vector<expr> m_stack;

    var_abs_rewriter (ast_manager &manager, obj_map<expr, expr*>& substitution,
                      unsigned k = 0) :
        m(manager), m_util(m), m_var_index(k),
        m_pinned(m), m_substitution(substitution) {}

    void reset(unsigned k = 0) {
        m_pinned.reset();
        m_var_index = k;
    }

    bool pre_visit(expr * t) {
        bool r = (!m_seen.is_marked(t) || m_has_num.is_marked(t));
        // only unify if convex closure will not contain non-linear multiplication
        if (m_util.is_mul(t))
        {
            bool contains_const_child = false;
            app* a = to_app(t);
            for (expr * arg : *a) {
                if (m_util.is_numeral(arg)) {
                    contains_const_child = true;
                }
            }
            if (!contains_const_child) {r = false;}
        }
        if (r) {m_stack.push_back (t);}
        return r;
    }


    br_status reduce_app (func_decl * f, unsigned num, expr * const * args,
                          expr_ref & result, proof_ref & result_pr) {
        expr *s;
        s = m_stack.back();
        m_stack.pop_back();
        if (is_app(s)) {
            app *a = to_app(s);
            for (unsigned i=0, sz = a->get_num_args(); i < sz; ++i) {
                if (m_has_num.is_marked(a->get_arg(i))) {
                    m_has_num.mark(a,true);
                    return BR_FAILED;
                }
            }
        }
        return BR_FAILED;
    }

    bool cache_all_results() const { return false; }
    bool cache_results() const { return false; }

    bool get_subst(expr * s, expr * & t, proof * & t_pr) {
        if (m_util.is_numeral(s)) {
            t = m.mk_var(m_var_index++, m.get_sort(s));
            m_substitution.insert(t, s);
            m_pinned.push_back(t);
            m_has_num.mark(s, true);
            m_seen.mark(t, true);
            return true;
        }
        return false;
    }

};


anti_unifier::anti_unifier(ast_manager &manager) : m(manager), m_pinned(m) {}

void anti_unifier::reset() {
    m_subs.reset();
    m_cache.reset();
    m_todo.reset();
    m_pinned.reset();
}

void anti_unifier::operator()(expr *e1, expr *e2, expr_ref &res,
                              substitution &s1, substitution &s2) {

    reset();
    if (e1 == e2) {res = e1; s1.reset(); s2.reset(); return;}

    m_todo.push_back(expr_pair(e1, e2));
    while (!m_todo.empty()) {
        const expr_pair &p = m_todo.back();
        SASSERT(is_app(p.first));
        SASSERT(is_app(p.second));

        app * n1 = to_app(p.first);
        app * n2 = to_app(p.second);

        unsigned num_arg1 = n1->get_num_args();
        unsigned num_arg2 = n2->get_num_args();
        if (n1->get_decl() != n2->get_decl() || num_arg1 != num_arg2) {
            expr_ref v(m);
            v = m.mk_var(m_subs.size(), get_sort(n1));
            m_pinned.push_back(v);
            m_subs.push_back(expr_pair(n1, n2));
            m_cache.insert(n1, n2, v);
        }
        else {
            expr *tmp;
            unsigned todo_sz = m_todo.size();
            ptr_buffer<expr> kids;
            for (unsigned i = 0; i < num_arg1; ++i) {
                expr *arg1 = n1->get_arg(i);
                expr *arg2 = n2->get_arg(i);
                if (arg1 == arg2) {kids.push_back(arg1);}
                else if (m_cache.find(arg1, arg2, tmp)) {kids.push_back(tmp);}
                else {m_todo.push_back(expr_pair(arg1, arg2));}
            }
            if (m_todo.size() > todo_sz) {continue;}

            expr_ref u(m);
            u = m.mk_app(n1->get_decl(), kids.size(), kids.c_ptr());
            m_pinned.push_back(u);
            m_cache.insert(n1, n2, u);
        }
    }

    expr *r;
    VERIFY(m_cache.find(e1, e2, r));
    res = r;

    // create substitutions
    s1.reserve(2, m_subs.size());
    s2.reserve(2, m_subs.size());

    for (unsigned i = 0, sz = m_subs.size(); i < sz; ++i) {
        expr_pair p = m_subs.get(i);
        s1.insert(i, 0, expr_offset(p.first, 1));
        s2.insert(i, 0, expr_offset(p.second, 1));
    }
}


class ncc_less_than_key
{
public:
    ncc_less_than_key(arith_util& util) : m_util(util) {}

    bool operator() (const expr*& e1, const expr*& e2) {
        rational val1;
        rational val2;

        if (m_util.is_numeral(e1, val1) && m_util.is_numeral(e2, val2))
        {
            return val1 < val2;
        }
        else
        {
            SASSERT(false);
            return false;
        }
    }
    arith_util m_util;
};

/*
 * if there is a single interval which exactly captures each of the
 * substitutions, return the corresponding closure, otherwise do
 * nothing
 */
bool naive_convex_closure::compute_closure(anti_unifier& au, ast_manager& m,
                                           expr_ref& result) {
    NOT_IMPLEMENTED_YET();
#if 0
    arith_util util(m);

    SASSERT(au.get_num_substitutions() > 0);
    if (au.get_substitution(0).size() == 0) {
        result = au.get_generalization();
        return true;
    }

    // check that all substitutions have the same size
    for (unsigned i=0, sz = au.get_num_substitutions(); i+1 < sz; ++i) {
        if (au.get_substitution(i).size() != au.get_substitution(i+1).size()) {
            return false;
        }
    }

    // for each substitution entry
    bool is_first_key = true;
    unsigned lower_bound = 0;
    unsigned upper_bound = 0;
    for (const auto& pair : au.get_substitution(0)) {
        // construct vector
        expr* key = &pair.get_key();
        vector<unsigned> entries;

        rational val;
        for (unsigned i=0, sz = au.get_num_substitutions(); i < sz; ++i)
        {
            if (util.is_numeral(au.get_substitution(i)[key], val) &&
                val.is_unsigned()) {
                entries.push_back(val.get_unsigned());
            }
            else {
                return false;
            }
        }

        // check whether vector represents interval
        unsigned current_lower_bound = 0;
        unsigned current_upper_bound = 0;

        // if vector represents interval
        if (get_range(entries, current_lower_bound, current_upper_bound)) {
            // if interval is the same as previous interval
            if (is_first_key) {
                is_first_key = false;
                lower_bound = current_lower_bound;
                upper_bound = current_upper_bound;
            }
            else {
                if (current_lower_bound != lower_bound ||
                    current_upper_bound != upper_bound) {
                    return false;
                }
            }
        }
        // otherwise we don't do a convex closure
        else {
            return false;
        }
    }

    // we finally know that we can express the substitutions using a
    // single interval, so build the expression 1. construct const
    expr_ref const_ref(m.mk_const(symbol("scti!0"), util.mk_int()), m);

    // 2. construct body with const
    expr_ref lit1(util.mk_le(util.mk_int(lower_bound), const_ref), m);
    expr_ref lit2(util.mk_le(const_ref, util.mk_int(upper_bound)), m);
    expr_ref lit3(m);
    substitute_vars_by_const(m, au.get_generalization(), const_ref, lit3);

    expr_ref_vector args(m);
    args.push_back(lit1);
    args.push_back(lit2);
    args.push_back(lit3);
    expr_ref body_with_consts = mk_and(args);

    // 3. replace const by var
    ptr_vector<expr> vars;
    vars.push_back(const_ref);

    expr_ref body(m);
    expr_abstract(m, 0, vars.size(), (expr*const*)vars.c_ptr(), body_with_consts, body);

    // 4. introduce quantifier
    ptr_vector<sort> sorts;
    sorts.push_back(util.mk_int());
    svector<symbol> names;
    names.push_back(symbol("scti!0"));

    result = expr_ref(m.mk_exists(vars.size(), sorts.c_ptr(), names.c_ptr(), body),m);

    return true;
#endif
}

bool naive_convex_closure::get_range(vector<unsigned int>& v,
                                     unsigned int& lower_bound, unsigned int& upper_bound)
{
    // sort substitutions
    std::sort(v.begin(), v.end());

    // check that numbers are consecutive
    for (unsigned i=0; i+1 < v.size(); ++i) {
        if (v[i] + 1 != v[i+1]) {
            return false;
        }
    }

    SASSERT(v.size() > 0);
    lower_bound = v[0];
    upper_bound = v.back();

    return true;
}

struct subs_rewriter_cfg : public default_rewriter_cfg {
    ast_manager &m;
    expr_ref m_c;

    subs_rewriter_cfg (ast_manager &manager, expr* c) : m(manager), m_c(c, m) {}

    bool reduce_var(var * t, expr_ref & result, proof_ref & result_pr) {
        result = m_c;
        result_pr = nullptr;
        return true;
    }
};

void naive_convex_closure::substitute_vars_by_const(ast_manager& m, expr* t,
                                                    expr* c, expr_ref& res) {
    subs_rewriter_cfg subs_cfg(m, c);
    rewriter_tpl<subs_rewriter_cfg> subs_rw (m, false, subs_cfg);
    subs_rw (t, res);
}


/// Construct a pattern by abstracting all numbers by variables
struct mk_num_pat_rewriter : public default_rewriter_cfg {
    ast_manager &m;
    arith_util m_arith;

    // -- mark already seen expressions
    ast_mark m_seen;
    // -- true if the expression is known to have a number as a sub-expression
    ast_mark m_has_num;
    // -- expressions created during the transformation
    expr_ref_vector m_pinned;
    // -- map from introduced variables to expressions they replace
    app_ref_vector &m_subs;


    // -- stack of expressions being processed to have access to expressions
    // -- before rewriting
    ptr_buffer<expr> m_stack;

    mk_num_pat_rewriter (ast_manager &manager, app_ref_vector& subs) :
        m(manager), m_arith(m), m_pinned(m), m_subs(subs) {}

    bool pre_visit(expr * t) {
        // -- don't touch multiplication
        if (m_arith.is_mul(t)) return false;

        bool r = (!m_seen.is_marked(t) || m_has_num.is_marked(t));
        if (r) {m_stack.push_back (t);}
        return r;
    }


    br_status reduce_app (func_decl * f, unsigned num, expr * const * args,
                          expr_ref & result, proof_ref & result_pr) {
        expr *s;
        s = m_stack.back();
        m_stack.pop_back();
        if (is_app(s)) {
            app *a = to_app(s);
            for (unsigned i = 0, sz = a->get_num_args(); i < sz; ++i) {
                if (m_has_num.is_marked(a->get_arg(i))) {
                    m_has_num.mark(a, true);
                    break;
                }
            }
        }
        return BR_FAILED;
    }

    bool cache_all_results() const { return false; }
    bool cache_results() const { return false; }

    bool get_subst(expr * s, expr * & t, proof * & t_pr) {
        if (m_arith.is_numeral(s)) {
            t = m.mk_var(m_subs.size(), m.get_sort(s));
            m_pinned.push_back(t);
            m_subs.push_back(to_app(s));

            m_has_num.mark(t, true);
            m_seen.mark(t, true);
            return true;
        }
        return false;
    }

};

void mk_num_pat(expr *e, expr_ref &result, app_ref_vector &subs) {
    SASSERT(subs.empty());
    mk_num_pat_rewriter rw_cfg(result.m(), subs);
    rewriter_tpl<mk_num_pat_rewriter> rw(result.m(), false, rw_cfg);
    rw(e, result);
}

}

template class rewriter_tpl<spacer::var_abs_rewriter>;
template class rewriter_tpl<spacer::subs_rewriter_cfg>;
template class rewriter_tpl<spacer::mk_num_pat_rewriter>;
