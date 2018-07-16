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
#include <typeinfo>
#include "ast/reg_decl_plugins.h"
#include "opt/opt_solver.h"
#include "smt/smt_context.h"
#include "smt/theory_arith.h"
#include "smt/theory_diff_logic.h"
#include "smt/theory_dense_diff_logic.h"
#include "smt/theory_pb.h"
#include "smt/theory_lra.h"
#include "ast/ast_pp.h"
#include "ast/ast_smt_pp.h"
#include "ast/pp_params.hpp"
#include "opt/opt_params.hpp"
#include "model/model_smt2_pp.h"
#include "util/stopwatch.h"

namespace opt {

    opt_solver::opt_solver(ast_manager & mgr, params_ref const & p, 
                           generic_model_converter& fm):
        solver_na2as(mgr),
        m_params(p),
        m_context(mgr, m_params),
        m(mgr),
        m_fm(fm),
        m_objective_terms(m),
        m_dump_benchmarks(false),
        m_first(true),
        m_was_unknown(false) {
        solver::updt_params(p);
        m_params.updt_params(p);
        if (m_params.m_case_split_strategy == CS_ACTIVITY_DELAY_NEW) {            
            m_params.m_relevancy_lvl = 0;
        }
        // m_params.m_auto_config = false;
    }

    unsigned opt_solver::m_dump_count = 0;
    
    opt_solver::~opt_solver() {
    }

    void opt_solver::updt_params(params_ref const & _p) {
        opt_params p(_p);
        m_dump_benchmarks = p.dump_benchmarks();
        m_params.updt_params(_p);
        m_context.updt_params(_p);
    }

    solver* opt_solver::translate(ast_manager& m, params_ref const& p) {
        UNREACHABLE();
        return nullptr;
    }

    void opt_solver::collect_param_descrs(param_descrs & r) {
        m_context.collect_param_descrs(r);
    }
    
    void opt_solver::collect_statistics(statistics & st) const {        
        m_context.collect_statistics(st);
    }
    
    void opt_solver::assert_expr_core(expr * t) {
        if (has_quantifiers(t)) {
            m_params.m_relevancy_lvl = 2;
        }
        m_context.assert_expr(t);
    }
    
    void opt_solver::push_core() {
        m_context.push();
    }
    
    void opt_solver::pop_core(unsigned n) {
        m_context.pop(n);
    }

    void opt_solver::set_logic(symbol const& logic) {
        m_logic = logic;
        m_context.set_logic(logic);
    }

    void opt_solver::ensure_pb() {
        smt::theory_id th_id = m.get_family_id("pb");
        smt::theory* th = get_context().get_theory(th_id);               
        if (!th) {
            get_context().register_plugin(alloc(smt::theory_pb, m, m_params));
        }
    }

    smt::theory_opt& opt_solver::get_optimizer() {
        smt::context& ctx = m_context.get_context();                        
        smt::theory_id arith_id = m_context.m().get_family_id("arith");     
        smt::theory* arith_theory = ctx.get_theory(arith_id);
        
        if (!arith_theory) {
            ctx.register_plugin(alloc(smt::theory_mi_arith, m, m_params));
            arith_theory = ctx.get_theory(arith_id);
            SASSERT(arith_theory);
        }
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
        else if (typeid(smt::theory_dense_mi&) == typeid(*arith_theory)) {   
            return dynamic_cast<smt::theory_dense_mi&>(*arith_theory); 
        }
        else if (typeid(smt::theory_dense_i&) == typeid(*arith_theory)) {   
            return dynamic_cast<smt::theory_dense_i&>(*arith_theory); 
        }
        else if (typeid(smt::theory_dense_smi&) == typeid(*arith_theory)) {   
            return dynamic_cast<smt::theory_dense_smi&>(*arith_theory); 
        }
        else if (typeid(smt::theory_dense_si&) == typeid(*arith_theory)) {   
            return dynamic_cast<smt::theory_dense_si&>(*arith_theory); 
        }
        else if (typeid(smt::theory_lra&) == typeid(*arith_theory)) {
            return dynamic_cast<smt::theory_lra&>(*arith_theory); 
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
        TRACE("opt_verbose", {
            tout << "context size: " << m_context.size() << "\n";            
            for (unsigned i = 0; i < m_context.size(); ++i) {
                tout << mk_pp(m_context.get_formula(i), m_context.m()) << "\n";
            }
        });
        stopwatch w;
        if (dump_benchmarks()) {
            w.start();
            std::stringstream file_name;
            file_name << "opt_solver" << ++m_dump_count << ".smt2";
            std::ofstream buffer(file_name.str().c_str());
            to_smt2_benchmark(buffer, num_assumptions, assumptions, "opt_solver");
            buffer.close();
            IF_VERBOSE(1, verbose_stream() << "(created benchmark: " << file_name.str() << "...";
                       verbose_stream().flush(););
        }
        lbool r;
        if (m_first && num_assumptions == 0 && m_context.get_scope_level() == 0) {
            r = m_context.setup_and_check();
        }
        else {
            r = m_context.check(num_assumptions, assumptions);
        }
        r = adjust_result(r);
        m_first = false;
        if (dump_benchmarks()) {
            w.stop();
            IF_VERBOSE(1, verbose_stream() << ".. " << r << " " << std::fixed << w.get_seconds() << ")\n";);
        }
        return r;
    }

    void opt_solver::maximize_objectives(expr_ref_vector& blockers) {
        expr_ref blocker(m);
        for (unsigned i = 0; i < m_objective_vars.size(); ++i) {
            maximize_objective(i, blocker);
            blockers.push_back(blocker);
        }
    }

    lbool opt_solver::find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) {
        return m_context.find_mutexes(vars, mutexes);
    }

    lbool opt_solver::preferred_sat(expr_ref_vector const& asms, vector<expr_ref_vector>& cores) {
        return m_context.preferred_sat(asms, cores);
    }



    /**
       \brief maximize the value of objective i in the current state.
       Return a predicate that blocks the current maximal value.
       
       The result of 'maximize' is post-processed. 
       When maximization involves shared symbols the model produced
       by local optimization does not necessarily satisfy combination 
       constraints (it may not be a real model).
       In this case, the model is post-processed (update_model 
       causes an additional call to final_check to propagate theory equalities
       when 'has_shared' is true).
       
    */
    void opt_solver::maximize_objective(unsigned i, expr_ref& blocker) {
        smt::theory_var v = m_objective_vars[i];
        bool has_shared = false;
        inf_eps val = get_optimizer().maximize(v, blocker, has_shared);
        get_model(m_model);
        inf_eps val2;
        m_valid_objectives[i] = true;
        TRACE("opt", tout << (has_shared?"has shared":"non-shared") << " " << val << "\n";);
        if (!m_models[i]) {
            set_model(i);
        }
        if (!val.is_finite()) {
            // skip model updates
        }
        else if (m_context.get_context().update_model(has_shared)) {
            if (has_shared && val != current_objective_value(i)) {
                decrement_value(i, val);
            }
            else {
                set_model(i);
            }
        }
        else {
            SASSERT(has_shared);
            decrement_value(i, val);
        }
        m_objective_values[i] = val;
        TRACE("opt", { 
                tout << "objective:     " << mk_pp(m_objective_terms[i].get(), m) << "\n";
                tout << "maximal value: " << val << "\n"; 
                tout << "new condition: " << blocker << "\n";
                if (m_models[i]) model_smt2_pp(tout << "update model:\n", m, *m_models[i], 0); });
    }

    void opt_solver::set_model(unsigned i) {
        model_ref mdl;
        get_model(mdl);
        m_models.set(i, mdl.get());
    }

    lbool opt_solver::decrement_value(unsigned i, inf_eps& val) {
        push_core();
        expr_ref ge = mk_ge(i, val);
        TRACE("opt", tout << ge << "\n";);
        assert_expr(ge);
        lbool is_sat = m_context.check(0, nullptr);
        is_sat = adjust_result(is_sat);
        if (is_sat == l_true) {
            set_model(i);
        }
        pop_core(1);
        TRACE("opt", tout << is_sat << "\n";);
        if (is_sat != l_true) {
            // cop-out approximation
            if (arith_util(m).is_real(m_objective_terms[i].get())) {
                val -= inf_eps(inf_rational(rational(0), true));
            }
            else {
                val -= inf_eps(inf_rational(rational(1)));
            }
            m_valid_objectives[i] = false;
        }
        return is_sat;

    }

    lbool opt_solver::adjust_result(lbool r) {
        if (r == l_undef && m_context.last_failure() == smt::QUANTIFIERS) {
            r = l_true;
            m_was_unknown = true;
        }
        return r;
    }
    
    void opt_solver::get_unsat_core(expr_ref_vector & r) {
        r.reset();
        unsigned sz = m_context.get_unsat_core_size();
        for (unsigned i = 0; i < sz; i++) {
            r.push_back(m_context.get_unsat_core_expr(i));
        }
    }

    void opt_solver::get_model_core(model_ref & m) {
        m_context.get_model(m);
        if (!m) m = m_model; else m_model = m;
    }
    
    proof * opt_solver::get_proof() {
        return m_context.get_proof();
    }
    
    std::string opt_solver::reason_unknown() const {
        return m_context.last_failure_as_string();
    }

    void opt_solver::set_reason_unknown(char const* msg) {
        m_context.set_reason_unknown(msg);
    }
    
    void opt_solver::get_labels(svector<symbol> & r) {
        r.reset();
        buffer<symbol> tmp;
        m_context.get_relevant_labels(nullptr, tmp);
        r.append(tmp.size(), tmp.c_ptr());
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
        return m_context.get_formula(idx);
    }
        
    smt::theory_var opt_solver::add_objective(app* term) {
        smt::theory_var v = get_optimizer().add_objective(term);
        m_objective_vars.push_back(v);
        m_objective_values.push_back(inf_eps(rational(-1), inf_rational()));
        m_objective_terms.push_back(term);
        m_valid_objectives.push_back(true);
        m_models.push_back(nullptr);
        return v;
    }
    
    vector<inf_eps> const& opt_solver::get_objective_values() {
        return m_objective_values;
    }

    inf_eps const& opt_solver::saved_objective_value(unsigned i) {
        return m_objective_values[i];
    }

    inf_eps opt_solver::current_objective_value(unsigned i) {
        smt::theory_var v = m_objective_vars[i];
        return get_optimizer().value(v);
    }
    
    expr_ref opt_solver::mk_ge(unsigned var, inf_eps const& val) {
        if (!val.is_finite()) {
            return expr_ref(val.is_pos() ? m.mk_false() : m.mk_true(), m);
        }
        smt::theory_opt& opt = get_optimizer();
        smt::theory_var v = m_objective_vars[var];
        TRACE("opt", tout << "v" << var << " " << val << "\n";);

        if (typeid(smt::theory_inf_arith) == typeid(opt)) {
            smt::theory_inf_arith& th = dynamic_cast<smt::theory_inf_arith&>(opt); 
            return th.mk_ge(m_fm, v, val);
        }

        if (typeid(smt::theory_mi_arith) == typeid(opt)) {
            smt::theory_mi_arith& th = dynamic_cast<smt::theory_mi_arith&>(opt); 
            SASSERT(val.is_finite());
            return th.mk_ge(m_fm, v, val.get_numeral());
        }

        if (typeid(smt::theory_i_arith) == typeid(opt)) {
            SASSERT(val.is_finite());
            SASSERT(val.get_infinitesimal().is_zero());
            smt::theory_i_arith& th = dynamic_cast<smt::theory_i_arith&>(opt); 
            return th.mk_ge(m_fm, v, val.get_rational());
        }

        if (typeid(smt::theory_idl) == typeid(opt)) {
            smt::theory_idl& th = dynamic_cast<smt::theory_idl&>(opt);
            return th.mk_ge(m_fm, v, val);
        }

        if (typeid(smt::theory_rdl) == typeid(opt) &&
            val.get_infinitesimal().is_zero()) {
            smt::theory_rdl& th = dynamic_cast<smt::theory_rdl&>(opt);
            return th.mk_ge(m_fm, v, val);
        }
        
        if (typeid(smt::theory_dense_i) == typeid(opt) &&
            val.get_infinitesimal().is_zero()) {
            smt::theory_dense_i& th = dynamic_cast<smt::theory_dense_i&>(opt);
            return th.mk_ge(m_fm, v, val);
        }

        if (typeid(smt::theory_dense_mi) == typeid(opt) &&
            val.get_infinitesimal().is_zero()) {
            smt::theory_dense_mi& th = dynamic_cast<smt::theory_dense_mi&>(opt);
            return th.mk_ge(m_fm, v, val);
        }


        if (typeid(smt::theory_lra) == typeid(opt)) {
            smt::theory_lra& th = dynamic_cast<smt::theory_lra&>(opt); 
            SASSERT(val.is_finite());
            return th.mk_ge(m_fm, v, val.get_numeral());            
        }

        // difference logic?
        if (typeid(smt::theory_dense_si) == typeid(opt) &&
            val.get_infinitesimal().is_zero()) {
            smt::theory_dense_si& th = dynamic_cast<smt::theory_dense_si&>(opt);
            return th.mk_ge(m_fm, v, val);
        }

        if (typeid(smt::theory_dense_smi) == typeid(opt) &&
            val.get_infinitesimal().is_zero()) {
            smt::theory_dense_smi& th = dynamic_cast<smt::theory_dense_smi&>(opt);
            return th.mk_ge(m_fm, v, val);
        }
        
        IF_VERBOSE(0, verbose_stream() << "WARNING: unhandled theory " << typeid(opt).name() << "\n";);
        return expr_ref(m.mk_true(), m);
    } 

    void opt_solver::reset_objectives() {
        m_objective_vars.reset();
        m_objective_values.reset();
        m_objective_terms.reset();
        m_valid_objectives.reset();
    }

    opt_solver& opt_solver::to_opt(solver& s) {
        if (typeid(opt_solver) != typeid(s)) {
            throw default_exception("BUG: optimization context has not been initialized correctly");
        }
        return dynamic_cast<opt_solver&>(s);
    }

    
    void opt_solver::to_smt2_benchmark(
        std::ofstream & buffer, 
        unsigned num_assumptions, 
        expr * const * assumptions,
        char const * name, 
        symbol const& logic,
        char const * status, 
        char const * attributes) {        
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
