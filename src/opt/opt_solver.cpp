/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_solver.cpp

Abstract:

    Wraps smt::kernel as a solver for optimization

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

    Based directly on smt_solver.
   
--*/
#include"reg_decl_plugins.h"
#include"opt_solver.h"
#include"smt_context.h"
#include"theory_arith.h"
#include"theory_diff_logic.h"

namespace opt {

    opt_solver::opt_solver(ast_manager & mgr, params_ref const & p, symbol const & l):
        solver_na2as(mgr),
        m_params(p),
        m_context(mgr, m_params),
        m(mgr),
        m_objective_enabled(false) {
        m_logic = l;
        if (m_logic != symbol::null)
            m_context.set_logic(m_logic);
    }
    
    opt_solver::~opt_solver() {
    }

    void opt_solver::updt_params(params_ref const & p) {
        m_params.updt_params(p);
        m_context.updt_params(p);
    }

    void opt_solver::collect_param_descrs(param_descrs & r) {
        m_context.collect_param_descrs(r);
    }
    
    void opt_solver::collect_statistics(statistics & st) const {
        m_context.collect_statistics(st);
    }
    
    void opt_solver::assert_expr(expr * t) {
        m_context.assert_expr(t);
    }
    
    void opt_solver::push_core() {
        m_context.push();
    }
    
    void opt_solver::pop_core(unsigned n) {
        m_context.pop(n);
    }


    smt::theory_opt& opt_solver::get_optimizer() {
        smt::context& ctx = m_context.get_context();                        
        smt::theory_id arith_id = m_context.m().get_family_id("arith");     
        smt::theory* arith_theory = ctx.get_theory(arith_id);               
        
        if (typeid(smt::theory_mi_arith) == typeid(*arith_theory)) {        
            return dynamic_cast<smt::theory_mi_arith&>(*arith_theory); 
        }                                                                   
        else if (typeid(smt::theory_i_arith) == typeid(*arith_theory)) {   
            return dynamic_cast<smt::theory_i_arith&>(*arith_theory); 
        }
        else if (typeid(smt::theory_inf_arith) == typeid(*arith_theory)) {   
            return dynamic_cast<smt::theory_inf_arith&>(*arith_theory); 
        }
        else if (typeid(smt::theory_rdl&) == typeid(*arith_theory)) {   
            return dynamic_cast<smt::theory_rdl&>(*arith_theory); 
        }
        else if (typeid(smt::theory_idl&) == typeid(*arith_theory)) {   
            return dynamic_cast<smt::theory_idl&>(*arith_theory); 
        }
        else {
            UNREACHABLE();
            return dynamic_cast<smt::theory_mi_arith&>(*arith_theory); 
        }
    }

    
    lbool opt_solver::check_sat_core(unsigned num_assumptions, expr * const * assumptions) {
        TRACE("opt_solver_na2as", tout << "opt_opt_solver::check_sat_core: " << num_assumptions << "\n";);
        lbool r = m_context.check(num_assumptions, assumptions);
        if (r == l_true && m_objective_enabled) {
            m_objective_values.reset();
            smt::theory_opt& opt = get_optimizer();
            for (unsigned i = 0; i < m_objective_vars.size(); ++i) {
                smt::theory_var v = m_objective_vars[i];
                m_objective_values.push_back(opt.maximize(v));
            }
        }
        return r;
    }
    
    void opt_solver::get_unsat_core(ptr_vector<expr> & r) {
        unsigned sz = m_context.get_unsat_core_size();
        for (unsigned i = 0; i < sz; i++)
            r.push_back(m_context.get_unsat_core_expr(i));
    }

    void opt_solver::get_model(model_ref & m) {
        m_context.get_model(m);
    }
    
    proof * opt_solver::get_proof() {
        return m_context.get_proof();
    }
    
    std::string opt_solver::reason_unknown() const {
        return m_context.last_failure_as_string();
    }
    
    void opt_solver::get_labels(svector<symbol> & r) {
        buffer<symbol> tmp;
        m_context.get_relevant_labels(0, tmp);
        r.append(tmp.size(), tmp.c_ptr());
    }
    
    void opt_solver::set_cancel(bool f) {
        m_context.set_cancel(f);
    }
    
    void opt_solver::set_progress_callback(progress_callback * callback) {
        m_callback = callback;
        m_context.set_progress_callback(callback);
    }
    
    unsigned opt_solver::get_num_assertions() const {
        return m_context.size();
    }
    
    expr * opt_solver::get_assertion(unsigned idx) const {
        SASSERT(idx < get_num_assertions());
        return m_context.get_formulas()[idx];
    }
    
    void opt_solver::display(std::ostream & out) const {
        m_context.display(out);
    }
    
    smt::theory_var opt_solver::add_objective(app* term) {
        m_objective_vars.push_back(get_optimizer().add_objective(term));
        return m_objective_vars.back();
    }
    
    vector<inf_eps> const& opt_solver::get_objective_values() {
        return m_objective_values;
    }
    
    expr_ref opt_solver::block_lower_bound(unsigned var, inf_eps const& val) {
        if (val.get_infinity().is_pos()) {
            return expr_ref(m.mk_false(), m);
        }
        else if (val.get_infinity().is_neg()) {
            return expr_ref(m.mk_true(), m);
        }
        else {
            inf_rational n = val.get_numeral();            
            return expr_ref(get_optimizer().block_lower_bound(m_objective_vars[var], n), m);
        }
    }

    void opt_solver::reset_objectives() {
        m_objective_vars.reset();
        m_objective_values.reset();
    }

    opt_solver::toggle_objective::toggle_objective(opt_solver& s, bool new_value): s(s), m_old_value(s.m_objective_enabled) {
        s.m_objective_enabled = new_value;
    }

    opt_solver::toggle_objective::~toggle_objective() {
        s.m_objective_enabled = m_old_value;
    }


}
