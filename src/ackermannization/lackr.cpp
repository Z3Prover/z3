/*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  lackr.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/

#include "ackermannization/lackr.h"
#include "ackermannization/ackermannization_params.hpp"
#include "tactic/tactic.h"
#include "ackermannization/lackr_model_constructor.h"
#include "ackermannization/ackr_info.h"
#include "ast/for_each_expr.h"
#include "model/model_smt2_pp.h"

lackr::lackr(ast_manager& m, params_ref p, lackr_stats& st, expr_ref_vector& formulas,
    solver * uffree_solver)
    : m_m(m)
    , m_p(p)
    , m_formulas(formulas)
    , m_abstr(m)
    , m_sat(uffree_solver)
    , m_ackr_helper(m)
    , m_simp(m)
    , m_ackrs(m)
    , m_st(st)
    , m_is_init(false)
{
    updt_params(p);
}

void lackr::updt_params(params_ref const & _p) {
    ackermannization_params p(_p);
    m_eager = p.eager();
}

lackr::~lackr() {
    const fun2terms_map::iterator e = m_fun2terms.end();
    for (fun2terms_map::iterator i = m_fun2terms.begin(); i != e; ++i) {
        dealloc(i->get_value());
    }
}

lbool lackr::operator() () {
    SASSERT(m_sat);
    if (!init()) return l_undef;
    const lbool rv = m_eager ? eager() : lazy();
    if (rv == l_true) m_sat->get_model(m_model);
    CTRACE("lackr", rv == l_true,
        model_smt2_pp(tout << "abstr_model(\n", m_m, *(m_model.get()), 2); tout << ")\n"; );
    return rv;
}

bool lackr::mk_ackermann(/*out*/goal_ref& g, double lemmas_upper_bound) {
    if (lemmas_upper_bound <= 0) return false;
    if (!init()) return false;
    if (lemmas_upper_bound != std::numeric_limits<double>::infinity()) {
        const double lemmas_bound = ackr_helper::calculate_lemma_bound(m_fun2terms);
        if (lemmas_bound > lemmas_upper_bound) return false;
    }
    eager_enc();
    for (unsigned i = 0; i < m_abstr.size(); ++i) g->assert_expr(m_abstr.get(i));
    for (unsigned i = 0; i < m_ackrs.size(); ++i) g->assert_expr(m_ackrs.get(i));
    return true;
}

bool lackr::init() {
    SASSERT(!m_is_init);    
    params_ref simp_p(m_p);
    m_simp.updt_params(simp_p);
    m_info = alloc(ackr_info, m_m);
    if (!collect_terms()) return false;
    abstract();
    m_is_init = true;
    return true;
}

//
// Introduce ackermann lemma for the two given terms.
//
bool lackr::ackr(app * const t1, app * const t2) {
    TRACE("lackr", tout << "ackr "
            << mk_ismt2_pp(t1, m_m, 2) << " , " << mk_ismt2_pp(t2, m_m, 2) << "\n";);
    const unsigned sz = t1->get_num_args();
    SASSERT(t2->get_num_args() == sz);
    expr_ref_vector eqs(m_m);
    for (unsigned i = 0; i < sz; ++i) {
        expr * const arg1 = t1->get_arg(i);
        expr * const arg2 = t2->get_arg(i);
        if (m_m.are_equal(arg1, arg2)) continue; // quickly skip syntactically equal
        if (m_m.are_distinct(arg1, arg2)){ // quickly abort if there are two distinct (e.g. numerals)                    
            TRACE("lackr", tout << "never eq\n";);
            return false;
        }
        eqs.push_back(m_m.mk_eq(arg1, arg2));
    }
    app * const a1 = m_info->get_abstr(t1);
    app * const a2 = m_info->get_abstr(t2);
    SASSERT(a1 && a2);
    TRACE("lackr", tout << "abstr1 " << mk_ismt2_pp(a1, m_m, 2) << "\n";);
    TRACE("lackr", tout << "abstr2 " << mk_ismt2_pp(a2, m_m, 2) << "\n";);
    expr_ref lhs(m_m);
    lhs = (eqs.size() == 1) ? eqs.get(0) : m_m.mk_and(eqs.size(), eqs.c_ptr());
    TRACE("lackr", tout << "ackr constr lhs" << mk_ismt2_pp(lhs, m_m, 2) << "\n";);
    expr_ref rhs(m_m.mk_eq(a1, a2),m_m);
    TRACE("lackr", tout << "ackr constr rhs" << mk_ismt2_pp(rhs, m_m, 2) << "\n";);
    expr_ref cg(m_m.mk_implies(lhs, rhs), m_m);
    TRACE("lackr", tout << "ackr constr" << mk_ismt2_pp(cg, m_m, 2) << "\n";);
    expr_ref cga(m_m);
    m_info->abstract(cg, cga); // constraint needs abstraction due to nested applications
    m_simp(cga);
    TRACE("lackr", tout << "ackr constr abs:" << mk_ismt2_pp(cga, m_m, 2) << "\n";);
    if (m_m.is_true(cga)) return false;
    m_st.m_ackrs_sz++;
    m_ackrs.push_back(cga);
    return true;
}

//
// Introduce the ackermann lemma for each pair of terms.
//
void lackr::eager_enc() {
    TRACE("lackr", tout << "#funs: " << m_fun2terms.size() << std::endl;);
    const fun2terms_map::iterator e = m_fun2terms.end();
    for (fun2terms_map::iterator i = m_fun2terms.begin(); i != e; ++i) {
        checkpoint();
        app_set * const  ts = i->get_value();
        const app_set::iterator r = ts->end();
        for (app_set::iterator j = ts->begin(); j != r; ++j) {
            app_set::iterator k = j;
            ++k;
            for (;  k != r; ++k) {
                app * const t1 = *j;
                app * const t2 = *k;
                SASSERT(t1->get_decl() == i->m_key);
                SASSERT(t2->get_decl() == i->m_key);
                if (t1 == t2) continue;
                ackr(t1,t2);
            }
        }
    }
}


void lackr::abstract() {
    const fun2terms_map::iterator e = m_fun2terms.end();
    for (fun2terms_map::iterator i = m_fun2terms.begin(); i != e; ++i) {
        func_decl* const fd = i->m_key;
        app_set * const ts = i->get_value();
        sort* const s = fd->get_range();
        const app_set::iterator r = ts->end();
        for (app_set::iterator j = ts->begin(); j != r; ++j) {
            app * const fc = m_m.mk_fresh_const(fd->get_name().str().c_str(), s);
            app * const t = *j;
            SASSERT(t->get_decl() == fd);
            m_info->set_abstr(t, fc);
            TRACE("lackr", tout << "abstr term "
                    << mk_ismt2_pp(t, m_m, 2)
                    << " -> "
                    << mk_ismt2_pp(fc, m_m, 2)
                    << "\n";);
        }
    }
    m_info->seal();
    // perform abstraction of the formulas
    const unsigned sz = m_formulas.size();
    for (unsigned i = 0; i < sz; ++i) {
        expr_ref a(m_m);
        m_info->abstract(m_formulas.get(i), a);
        m_abstr.push_back(a);
    }
}

void lackr::add_term(app* a) {
    if (a->get_num_args() == 0) return;
    if (!m_ackr_helper.should_ackermannize(a)) return;
    func_decl* const fd = a->get_decl();
    app_set* ts = nullptr;
    if (!m_fun2terms.find(fd, ts)) {
        ts = alloc(app_set);
        m_fun2terms.insert(fd, ts);
    }
    TRACE("lackr", tout << "term(" << mk_ismt2_pp(a, m_m, 2) << ")\n";);
    ts->insert(a);
}

void  lackr::push_abstraction() {
    const unsigned sz = m_abstr.size();
    for (unsigned i = 0; i < sz; ++i) {
        m_sat->assert_expr(m_abstr.get(i));
    }
}

lbool lackr::eager() {
    SASSERT(m_is_init);
    push_abstraction();
    TRACE("lackr", tout << "run sat 0\n"; );
    const lbool rv0 = m_sat->check_sat(0, nullptr);
    if (rv0 == l_false) return l_false;
    eager_enc();
    expr_ref all(m_m);
    all = m_m.mk_and(m_ackrs.size(), m_ackrs.c_ptr());
    m_simp(all);
    m_sat->assert_expr(all);
    TRACE("lackr", tout << "run sat all\n"; );
    return m_sat->check_sat(0, nullptr);
}

lbool lackr::lazy() {
    SASSERT(m_is_init);
    lackr_model_constructor mc(m_m, m_info);
    push_abstraction();
    unsigned ackr_head = 0;
    while (1) {
        m_st.m_it++;
        checkpoint();
        TRACE("lackr", tout << "lazy check: " << m_st.m_it << "\n";);
        const lbool r = m_sat->check_sat(0, nullptr);
        if (r == l_undef) return l_undef; // give up
        if (r == l_false) return l_false; // abstraction unsat
        // reconstruct model
        model_ref am;
        m_sat->get_model(am);
        const bool mc_res = mc.check(am);
        if (mc_res) return l_true; // model okay
        // refine abstraction
        const lackr_model_constructor::conflict_list conflicts = mc.get_conflicts();
        for (lackr_model_constructor::conflict_list::const_iterator i = conflicts.begin();
             i != conflicts.end(); ++i) {
            ackr(i->first, i->second);
        }
        while (ackr_head < m_ackrs.size()) {
            m_sat->assert_expr(m_ackrs.get(ackr_head++));
        }
    }
}

//
// Collect all uninterpreted terms, skipping 0-arity.
//
bool lackr::collect_terms() {
    ptr_vector<expr> stack;
    expr *           curr;
    expr_mark        visited;
    for(unsigned i = 0; i < m_formulas.size(); ++i) {
        stack.push_back(m_formulas.get(i));
        TRACE("lackr", tout << "infla: " <<mk_ismt2_pp(m_formulas.get(i), m_m, 2) <<  "\n";);
    }

    while (!stack.empty()) {
        curr = stack.back();
        if (visited.is_marked(curr)) {
            stack.pop_back();
            continue;
        }

        switch (curr->get_kind()) {
            case AST_VAR:
                visited.mark(curr, true);
                stack.pop_back();
                break;
            case AST_APP:
            {
                app * const a = to_app(curr);
                if (for_each_expr_args(stack, visited, a->get_num_args(), a->get_args())) {
                    visited.mark(curr, true);
                    stack.pop_back();
                    add_term(a);
                }
            }
                break;
            case AST_QUANTIFIER:
                return false; // quantifiers not supported
            default:
                UNREACHABLE();
                return false;
        }
    }
    return true;
}
