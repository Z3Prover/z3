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
#include "reg_decl_plugins.h"
#include "opt_solver.h"
#include "smt_context.h"
#include "theory_arith.h"
#include "theory_diff_logic.h"
#include "theory_pb.h"
#include "ast_pp.h"
#include "ast_smt_pp.h"
#include "pp_params.hpp"
#include "opt_params.hpp"
#include "model_smt2_pp.h"

namespace opt {

    opt_solver::opt_solver(ast_manager & mgr, params_ref const & p, symbol const & l):
        solver_na2as(mgr),
        m_params(p),
        m_context(mgr, m_params),
        m(mgr),
        m_dump_benchmarks(false),
        m_fm(m) {
        m_logic = l;
        if (m_logic != symbol::null)
            m_context.set_logic(m_logic);
    }

    unsigned opt_solver::m_dump_count = 0;
    
    opt_solver::~opt_solver() {
    }

    void opt_solver::updt_params(params_ref & _p) {
        opt_params p(_p);
        m_dump_benchmarks = p.dump_benchmarks();
        m_params.updt_params(_p);
        m_context.updt_params(_p);
        smt::theory_id th_id = m.get_family_id("pb");
        smt::theory* _th = get_context().get_theory(th_id);               
        if (_th) {
            smt::theory_pb* th = dynamic_cast<smt::theory_pb*>(_th);
            th->set_conflict_frequency(p.pb_conflict_freq());
            th->set_learn_complements(p.pb_learn_comp());
        }            
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

    bool opt_solver::dump_benchmarks() {
        return m_dump_benchmarks;
    }

    lbool opt_solver::check_sat_core(unsigned num_assumptions, expr * const * assumptions) {
        TRACE("opt", {
            tout << "context size: " << m_context.size() << "\n";            
            for (unsigned i = 0; i < m_context.size(); ++i) {
                tout << mk_pp(m_context.get_formulas()[i], m_context.m()) << "\n";
            }
        });
        if (dump_benchmarks()) {
            std::stringstream file_name;
            file_name << "opt_solver" << ++m_dump_count << ".smt2";
            std::ofstream buffer(file_name.str().c_str());
            to_smt2_benchmark(buffer, num_assumptions, assumptions, "opt_solver", "");
            buffer.close();
        }
        return m_context.check(num_assumptions, assumptions);
    }

    void opt_solver::maximize_objectives() {
        for (unsigned i = 0; i < m_objective_vars.size(); ++i) {
            maximize_objective(i);
        }
    }

    void opt_solver::maximize_objective(unsigned i) {
        smt::theory_var v = m_objective_vars[i];
        m_objective_values[i] = get_optimizer().maximize(v);
        m_context.get_context().update_model();        
        TRACE("opt", { model_ref mdl; get_model(mdl); model_smt2_pp(tout << "update model: ", m, *mdl, 0); });
    }
    
    void opt_solver::get_unsat_core(ptr_vector<expr> & r) {
        unsigned sz = m_context.get_unsat_core_size();
        for (unsigned i = 0; i < sz; i++) {
            r.push_back(m_context.get_unsat_core_expr(i));
        }
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
        m_objective_values.push_back(inf_eps(rational(-1), inf_rational()));
        return m_objective_vars.back();
    }
    
    vector<inf_eps> const& opt_solver::get_objective_values() {
        return m_objective_values;
    }

    inf_eps const& opt_solver::get_objective_value(unsigned i) {
        return m_objective_values[i];
    }

    expr_ref opt_solver::mk_ge(unsigned var, inf_eps const& val) {
        smt::theory_opt& opt = get_optimizer();
        smt::theory_var v = m_objective_vars[var];

        if (typeid(smt::theory_inf_arith) == typeid(opt)) {
            smt::theory_inf_arith& th = dynamic_cast<smt::theory_inf_arith&>(opt); 
            return expr_ref(th.mk_ge(m_fm, v, val), m);
        }

        if (typeid(smt::theory_mi_arith) == typeid(opt)) {
            smt::theory_mi_arith& th = dynamic_cast<smt::theory_mi_arith&>(opt); 
            SASSERT(val.is_finite());
            return expr_ref(th.mk_ge(m_fm, v, val.get_numeral()), m);
        }

        if (typeid(smt::theory_i_arith) == typeid(opt)) {
            SASSERT(val.is_finite());
            SASSERT(val.get_infinitesimal().is_zero());
            smt::theory_i_arith& th = dynamic_cast<smt::theory_i_arith&>(opt); 
            return expr_ref(th.mk_ge(m_fm, v, val.get_rational()), m);
        }

        // difference logic?
        return expr_ref(m.mk_true(), m);
    }
 
    expr_ref opt_solver::mk_gt(unsigned var, inf_eps const& val) {
        if (val.get_infinity().is_pos()) {
            return expr_ref(m.mk_false(), m);
        }
        else if (val.get_infinity().is_neg()) {
            return expr_ref(m.mk_true(), m);
        }
        else {
            inf_rational n = val.get_numeral();            
            return expr_ref(get_optimizer().mk_gt(m_objective_vars[var], n), m);
        }
    }

    void opt_solver::reset_objectives() {
        m_objective_vars.reset();
        m_objective_values.reset();
    }

    opt_solver& opt_solver::to_opt(solver& s) {
        if (typeid(opt_solver) != typeid(s)) {
            throw default_exception("BUG: optimization context has not been initialized correctly");
        }
        return dynamic_cast<opt_solver&>(s);
    }

    
    void opt_solver::to_smt2_benchmark(std::ofstream & buffer, 
                                       unsigned num_assumptions, expr * const * assumptions,
                                       char const * name, char const * logic, 
                                       char const * status, char const * attributes) {        
        ast_smt_pp pp(m);
        pp.set_benchmark_name(name);
        pp.set_logic(logic);
        pp.set_status(status);
        pp.add_attributes(attributes);
        pp_params params;
        pp.set_simplify_implies(params.simplify_implies());

        for (unsigned i = 0; i < num_assumptions; ++i) {
            pp.add_assumption(assumptions[i]);
        }
        for (unsigned i = 0; i < get_num_assertions(); ++i) {
            pp.add_assumption(get_assertion(i));
        }
        pp.display_smt2(buffer, m.mk_true());        
    }


}
