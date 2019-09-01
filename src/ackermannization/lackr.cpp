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
#include "ast/ast_util.h"
#include "model/model_smt2_pp.h"

lackr::lackr(ast_manager& m, const params_ref& p, lackr_stats& st,
             const ptr_vector<expr>& formulas, solver * uffree_solver)
    : m(m),
      m_p(p),
      m_formulas(formulas),
      m_autil(m),
      m_abstr(m),
      m_solver(uffree_solver),
      m_ackr_helper(m),
      m_simp(m),
      m_ackrs(m),
      m_st(st),
      m_is_init(false)
{
    updt_params(p);
}

void lackr::updt_params(params_ref const & _p) {
    ackermannization_params p(_p);
    m_eager = p.eager();
}

lackr::~lackr() {    
    for (auto& kv : m_fun2terms) {
        dealloc(kv.get_value());
    }
    for (auto& kv : m_sel2terms) {
        dealloc(kv.get_value());
    }
}

lbool lackr::operator()() {
    SASSERT(m_solver);
    if (!init()) 
        return l_undef;
    lbool rv = m_eager ? eager() : lazy();
    if (rv == l_true) {
        m_solver->get_model(m_model);
    }
    CTRACE("ackermannize", rv == l_true, model_smt2_pp(tout << "abstr_model(\n", m, *(m_model.get()), 2); tout << ")\n"; );
    return rv;
}

bool lackr::mk_ackermann(/*out*/goal_ref& g, double lemmas_upper_bound) {    
    if (lemmas_upper_bound <= 0)
        return false;
    if (!init())
        return false;
    if (lemmas_upper_bound != std::numeric_limits<double>::infinity() &&
        ackr_helper::calculate_lemma_bound(m_fun2terms, m_sel2terms) > lemmas_upper_bound) 
        return false;
    eager_enc();
    for (expr* a : m_abstr) 
        g->assert_expr(a);
    for (expr* a : m_ackrs) 
        g->assert_expr(a);
    return true;
}

bool lackr::init() {
    if (!m_is_init) {
        params_ref simp_p(m_p);
        m_simp.updt_params(simp_p);
        m_info = alloc(ackr_info, m);
        if (!collect_terms()) 
            return false;
        abstract();
        m_is_init = true;
    }
    return true;
}

//
// Introduce ackermann lemma for the two given terms.
//
bool lackr::ackr(app * const t1, app * const t2) {
    TRACE("ackermannize", tout << "ackr " << mk_ismt2_pp(t1, m, 2) << " , " << mk_ismt2_pp(t2, m, 2) << "\n";);
    const unsigned sz = t1->get_num_args();
    SASSERT(t2->get_num_args() == sz);
    expr_ref_vector eqs(m);
    for (unsigned i = 0; i < sz; ++i) {
        expr * const arg1 = t1->get_arg(i);
        expr * const arg2 = t2->get_arg(i);
        if (m.are_equal(arg1, arg2)) continue; // quickly skip syntactically equal
        if (m.are_distinct(arg1, arg2)){ // quickly abort if there are two distinct (e.g. numerals)                    
            TRACE("ackermannize", tout << "never eq\n";);
            return false;
        }
        eqs.push_back(m.mk_eq(arg1, arg2));
    }
    app * const a1 = m_info->get_abstr(t1);
    app * const a2 = m_info->get_abstr(t2);
    SASSERT(a1 && a2);
    expr_ref lhs = mk_and(eqs);
    expr_ref rhs(m.mk_eq(a1, a2),m);
    expr_ref cg(m.mk_implies(lhs, rhs), m);
    expr_ref cga = m_info->abstract(cg); // constraint needs abstraction due to nested applications
    m_simp(cga);
    TRACE("ackermannize", 
          tout << "abstr1 " << mk_ismt2_pp(a1, m, 2) << "\n";
          tout << "abstr2 " << mk_ismt2_pp(a2, m, 2) << "\n";
          tout << "ackr constr lhs" << mk_ismt2_pp(lhs, m, 2) << "\n";
          tout << "ackr constr rhs" << mk_ismt2_pp(rhs, m, 2) << "\n";
          tout << "ackr constr" << mk_ismt2_pp(cg, m, 2) << "\n";
          tout << "ackr constr abs:" << mk_ismt2_pp(cga, m, 2) << "\n";);
    if (m.is_true(cga)) {
        return false;
    }
    m_st.m_ackrs_sz++;
    m_ackrs.push_back(std::move(cga));
    return true;
}

//
// Introduce the ackermann lemma for each pair of terms.
//
void lackr::eager_enc() {
    TRACE("ackermannize", tout << "#funs: " << m_fun2terms.size() << "#sels: " << m_sel2terms.size() << std::endl;);
    for (auto const& kv : m_fun2terms) {
        checkpoint();
        ackr(kv.get_value());
    }
    for (auto const& kv : m_sel2terms) {
        checkpoint();
        ackr(kv.get_value());
    }
}

void lackr::ackr(app_set const* ts) {
    const app_set::iterator r = ts->end();
    for (app_set::iterator j = ts->begin(); j != r; ++j) {
        app * const t1 = *j;
        app_set::iterator k = j;
        ++k;
        for (; k != r; ++k) {
            app * const t2 = *k;
            if (t1 != t2) {
                ackr(t1, t2);
            }
        }
    }
}


void lackr::abstract() {
    for (auto const& kv : m_fun2terms) {
        func_decl* fd = kv.m_key;
        for (app * t : *kv.m_value) {
            app * fc = m.mk_fresh_const(fd->get_name(), m.get_sort(t));
            SASSERT(t->get_decl() == fd);
            m_info->set_abstr(t, fc);
        }
    }

    for (auto& kv : m_sel2terms) {
        func_decl * fd = kv.m_key->get_decl();
        for (app * t : *kv.m_value) {
            app * fc = m.mk_fresh_const(fd->get_name(), m.get_sort(t));
            m_info->set_abstr(t, fc);
        }
    }
    m_info->seal();
    // perform abstraction of the formulas
    for (expr * f : m_formulas) {
        expr_ref a = m_info->abstract(f);
        m_abstr.push_back(std::move(a));
    }
}

void lackr::add_term(app* a) {
    app_set* ts = nullptr;
    if (a->get_num_args() == 0) 
        return;
    if (m_ackr_helper.is_select(a)) {
        app* sel = to_app(a->get_arg(0));
        if (!m_sel2terms.find(sel, ts)) {
            ts = alloc(app_set);
            m_sel2terms.insert(sel, ts);
        }
    }
    else if (m_ackr_helper.is_uninterp_fn(a)) {
        func_decl* const fd = a->get_decl();
        if (!m_fun2terms.find(fd, ts)) {
            ts = alloc(app_set);
            m_fun2terms.insert(fd, ts);
        }
    }
    else {
        return;
    }
    TRACE("ackermannize", tout << "term(" << mk_ismt2_pp(a, m, 2) << ")\n";);
    ts->insert(a);
}

void  lackr::push_abstraction() {
    for (expr* a : m_abstr) {
        m_solver->assert_expr(a);
    }
}

lbool lackr::eager() {
    SASSERT(m_is_init);
    push_abstraction();
    TRACE("ackermannize", tout << "run sat 0\n"; );
    lbool rv0 = m_solver->check_sat(0, nullptr);
    if (rv0 == l_false) {
        return l_false;
    }
    eager_enc();
    expr_ref all = mk_and(m_ackrs);
    m_simp(all);
    m_solver->assert_expr(all);
    TRACE("ackermannize", tout << "run sat all\n"; );
    return m_solver->check_sat(0, nullptr);
}

lbool lackr::lazy() {
    SASSERT(m_is_init);
    lackr_model_constructor mc(m, m_info);
    push_abstraction();
    unsigned ackr_head = 0;
    while (true) {
        m_st.m_it++;
        checkpoint();
        TRACE("ackermannize", tout << "lazy check: " << m_st.m_it << "\n";);
        const lbool r = m_solver->check_sat(0, nullptr);
        if (r == l_undef) return l_undef; // give up
        if (r == l_false) return l_false; // abstraction unsat
        // reconstruct model
        model_ref am;
        m_solver->get_model(am);
        const bool mc_res = mc.check(am);
        if (mc_res) return l_true; // model okay
        // refine abstraction
        for (auto const& kv : mc.get_conflicts()) {
            ackr(kv.first, kv.second);
        }
        while (ackr_head < m_ackrs.size()) {
            m_solver->assert_expr(m_ackrs.get(ackr_head++));
        }
    }
}

//
// Collect all uninterpreted terms, skipping 0-arity.
//
bool lackr::collect_terms() {
    ptr_vector<expr> stack = m_formulas;
    expr_mark        visited;

    while (!stack.empty()) {
        expr * curr = stack.back();
        if (visited.is_marked(curr)) {
            stack.pop_back();
            continue;
        }
        switch (curr->get_kind()) {
            case AST_VAR:
                visited.mark(curr, true);
                stack.pop_back();
                break;
            case AST_APP: {
                app * const a = to_app(curr);
                if (for_each_expr_args(stack, visited, a->get_num_args(), a->get_args())) {
                    visited.mark(curr, true);
                    stack.pop_back();
                    m_ackr_helper.mark_non_select(a, m_non_select);
                    add_term(a);
                }                
                break;
            }
            case AST_QUANTIFIER:
                return false; // quantifiers not supported
            default:
                UNREACHABLE();
                return false;
        }
    }

    m_ackr_helper.prune_non_select(m_sel2terms, m_non_select);
    
    return true;
}
