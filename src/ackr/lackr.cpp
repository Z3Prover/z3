/*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  lackr.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
///////////////
#include"lackr.h"
#include"ackr_params.hpp"
#include"tactic.h"
#include"lackr_model_constructor.h"
#include"ackr_info.h"
#include"for_each_expr.h"
///////////////
#include"inc_sat_solver.h"
#include"qfaufbv_tactic.h"
#include"qfbv_tactic.h"
#include"tactic2solver.h"
///////////////
#include"model_smt2_pp.h"
///////////////
lackr::lackr(ast_manager& m, params_ref p, lackr_stats& st, expr_ref_vector& formulas)
    : m_m(m)
    , m_p(p)
    , m_formulas(formulas)
    , m_abstr(m)
    , m_sat(0)
    , m_bvutil(m)
    , m_simp(m)
    , m_ackrs(m) 
    , m_st(st)
{
    updt_params(p);
}

lackr::~lackr() {
    const fun2terms_map::iterator e = m_fun2terms.end();
    for (fun2terms_map::iterator i = m_fun2terms.begin(); i != e; ++i) {
        dealloc(i->get_value());
    }
}

lbool lackr::operator() () {
    setup_sat();
    init();    
    const lbool rv = m_eager ? eager() : lazy();
    if (rv == l_true) m_sat->get_model(m_model);
    CTRACE("lackr", rv == l_true,
        model_smt2_pp(tout << "abstr_model(\n", m_m, *(m_model.get()), 2); tout << ")\n"; );
    return rv;
}

void lackr::init() {
    params_ref simp_p(m_p);
    m_simp.updt_params(simp_p);
    m_info = alloc(ackr_info, m_m);
    collect_terms();
    abstract();
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
    for (unsigned gi = 0; gi < sz; ++gi) {
        expr * const arg1 = t1->get_arg(gi);
        expr * const arg2 = t2->get_arg(gi);
        if (arg1 == arg2) continue;
        if (m_bvutil.is_numeral(arg1) && m_bvutil.is_numeral(arg2)) {
            SASSERT(arg1 != arg2);
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
    expr_ref lhs(m_m.mk_and(eqs.size(), eqs.c_ptr()), m_m);
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
    const fun2terms_map::iterator e = m_fun2terms.end();
    for (fun2terms_map::iterator i = m_fun2terms.begin(); i != e; ++i) {
        checkpoint();
        func_decl* const fd = i->m_key;
        app_set * const  ts = i->get_value();
        const app_set::iterator r = ts->end();
        for (app_set::iterator j = ts->begin(); j != r; ++j) {
            app_set::iterator k = j;
            ++k;
            for (;  k != r; ++k) {
                app * const t1 = *j;
                app * const t2 = *k;
                SASSERT(t1->get_decl() == fd);
                SASSERT(t2->get_decl() == fd);
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
    func_decl* const fd = a->get_decl();
    if (!is_uninterp(a)) return;
    SASSERT(m_bvutil.is_bv_sort(fd->get_range()) || m_m.is_bool(a));
    app_set* ts = 0;
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
    push_abstraction();
    TRACE("lackr", tout << "run sat 0\n"; );
    const lbool rv0 = m_sat->check_sat(0, 0);
    if (rv0 == l_false) return l_false;    
    eager_enc();
    expr_ref all(m_m);
    all = m_m.mk_and(m_ackrs.size(), m_ackrs.c_ptr());
    m_simp(all);    
    m_sat->assert_expr(all);
    TRACE("lackr", tout << "run sat all\n"; );
    return m_sat->check_sat(0, 0);
}

lbool lackr::lazy() {
    lackr_model_constructor mc(m_m, m_info);
    push_abstraction();
    unsigned ackr_head = 0;    
    while (1) {
        m_st.m_it++;
        checkpoint();
        TRACE("lackr", tout << "lazy check: " << m_st.m_it << "\n";);
        const lbool r = m_sat->check_sat(0, 0);
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

void lackr::setup_sat() {
    if (m_use_sat) {        
        tactic_ref t = mk_qfbv_tactic(m_m, m_p);
        m_sat = mk_tactic2solver(m_m, t.get(), m_p);
    }
    else {
        tactic_ref t = mk_qfaufbv_tactic(m_m, m_p);
        m_sat = mk_tactic2solver(m_m, t.get(), m_p);
    }
    SASSERT(m_sat);
    m_sat->set_produce_models(true);
}


//
// Collect all uninterpreted terms, skipping 0-arity.
//
void lackr::collect_terms() {
    ptr_vector<expr> stack;
    expr *           curr;
    expr_mark        visited;
    for(unsigned i = 0; i < m_formulas.size(); ++i) {
        stack.push_back(m_formulas.get(i));
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
                UNREACHABLE();
                break;
            default:
                UNREACHABLE();
                return;
        }
    }
    visited.reset();    
}
