/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt_solver_exp.cpp

Abstract:

    SMT solver using strategies and search on top of sat::solver
    This solver uses assertion_set strategies during restarts.
    
    It also uses the sat::solver to handle the Boolean structure of the problem.
    
    
Author:

    Leonardo de Moura (leonardo) 2011-06-25.

Revision History:
    This was an experiment to rewrite Z3 kernel.
    It will be deleted after we finish revamping Z3 kernel.

--*/
#include"smt_solver_exp.h"
#include"sat_solver.h"
#include"ast_translation.h"
#include"model.h"

namespace smt {
    
    void solver_exp::bridge::get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r) {
    }
    
    void solver_exp::bridge::asserted(sat::literal l) {
    }

    sat::check_result solver_exp::bridge::check() {
        return sat::CR_DONE;
    }

    void solver_exp::bridge::push() {
    }

    void solver_exp::bridge::pop(unsigned n) {
    }
    
    void solver_exp::bridge::simplify() {
    }

    void solver_exp::bridge::clauses_modifed() {
    }

    lbool solver_exp::bridge::get_phase(sat::bool_var v) {
        return l_undef;
    }

    solver_exp::solver_exp(ast_manager & ext_mng, params_ref const & p):
        m_ext_mng(ext_mng),
        m(ext_mng, true /* disable proof gen */),
        m_compiler(*this, p),
        m_assertions(m),
        m_atom2bvar(m),
        m_arith(m, p),
        m_bridge(*this) {
        updt_params_core(p);
        m_cancel = false;
    }

    solver_exp::~solver_exp() {
    }

    void solver_exp::updt_params_core(params_ref const & p) {
        m_params = p;
    }

    void solver_exp::updt_params(params_ref const & p) {
        updt_params_core(p);
        m_arith.updt_params(p);
        if (m_sat)
            m_sat->updt_params(p);
    }
    
    void solver_exp::collect_param_descrs(param_descrs & d) {
        // TODO
    }

    void solver_exp::set_cancel(bool f) {
        m_cancel = f;
        #pragma omp critical (smt_solver_exp)
        {
            if (m_sat) {
                m_sat->set_cancel(f);
            }
        }
        m_arith.set_cancel(f);
        m_compiler.set_cancel(f);
    }

    void solver_exp::init() {
        m_atom2bvar.reset();
        if (m_sat)
            m_sat->collect_statistics(m_stats);
        #pragma omp critical (smt_solver_exp)
        {
            m_sat = alloc(sat::solver, m_params, &m_bridge);
        }
        m_arith.collect_statistics(m_stats);
        m_arith.reset();
        set_cancel(m_cancel);
    }

    void solver_exp::assert_expr_core(expr * t, ast_translation & translator) {
        expr * new_t = translator(t);
        m_assertions.assert_expr(new_t);
    }
    
    /**
       \brief Assert an expression t (owned by the external manager)
    */
    void solver_exp::assert_expr(expr * t) {
        ast_translation translator(m_ext_mng, m, false);
        assert_expr_core(t, translator);
    }

    /**
       \brief Assert an assertion set s (owned by the external manager)
    */
    void solver_exp::assert_set(assertion_set const & s) {
        SASSERT(&(s.m()) == &m_ext_mng);
        ast_translation translator(m_ext_mng, m, false);
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++) {
            assert_expr_core(s.form(i), translator);
        }
    }

    void solver_exp::assert_goal(goal const & g) {
        SASSERT(&(g.m()) == &m_ext_mng);
        ast_translation translator(m_ext_mng, m, false);
        unsigned sz = g.size();
        for (unsigned i = 0; i < sz; i++) {
            assert_expr_core(g.form(i), translator);
        }
    }

    /**
       \brief Store in r the current set of assertions.
       r is (owned) by the external assertion set
    */
    void solver_exp::get_assertions(assertion_set & r) {
        SASSERT(&(r.m()) == &m_ext_mng);
        ast_translation translator(m, m_ext_mng, false);
        unsigned sz = m_assertions.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * f = m_assertions.form(i);
            r.assert_expr(translator(f));
        }
    }

    void solver_exp::get_model_converter(model_converter_ref & mc) {
        ast_translation translator(m, m_ext_mng, false);
        if (m_mc)
            mc = m_mc->translate(translator);
        else
            mc = 0;
    }

    // -----------------------
    //
    // Search
    //
    // -----------------------
    lbool solver_exp::check() {
        compile();
        lbool r = m_arith.check();
        if (r == l_false)
            return r;
        if (m_sat->num_vars() == 0 && r == l_true) {
            model_ref md = alloc(model, m);
            m_arith.mk_model(md.get());
            if (m_mc)
                (*m_mc)(md);
            ast_translation translator(m, m_ext_mng, false);
            m_model = md->translate(translator); 
            return l_true;
        }
        return l_undef;
    }

    void solver_exp::compile() {
        m_compiler();
    }

    // -----------------------
    //
    // Pretty Printing
    //
    // -----------------------
    void solver_exp::display(std::ostream & out) const {
        m_assertions.display(out);
    }

    void solver_exp::display_state(std::ostream & out) const {
        if (m_sat) m_sat->display(out);
        m_arith.display(out);
    }

    // -----------------------
    //
    // Statistics
    //
    // -----------------------
    void solver_exp::collect_statistics(statistics & st) const {
        solver_exp * _this = const_cast<solver_exp*>(this);
        if (m_sat) {
            m_sat->collect_statistics(_this->m_stats);
            m_sat->reset_statistics();
        }
        m_arith.collect_statistics(_this->m_stats);
        _this->m_arith.reset_statistics();
        st.copy(m_stats);
    }
    
    void solver_exp::reset_statistics() {
        m_stats.reset();
    }
    

};


