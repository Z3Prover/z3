/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_solver_strategy.cpp

Abstract:

    Strategy for using the SAT solver preprocessing capabilities.
    
Author:

    Leonardo (leonardo) 2011-05-23

Notes:

--*/
#include"sat_solver_strategy.h"
#include"assertion_set2sat.h"
#include"sat_solver.h"
#include"filter_model_converter.h"
#include"ast_smt2_pp.h"
#include"model_v2_pp.h"

struct sat_solver_strategy::imp {
    ast_manager &     m;
    assertion_set2sat m_as2sat;
    sat2assertion_set m_sat2as;
    sat::solver       m_solver;
    params_ref        m_params;
    bool              m_produce_models;
    
    imp(ast_manager & _m, params_ref const & p):
        m(_m),
        m_solver(p, 0),
        m_params(p) {
        SASSERT(!m.proofs_enabled());
        m_produce_models = p.get_bool(":produce-models", false);
    }

    void operator()(assertion_set & s, model_converter_ref & mc) {
        if (s.m().proofs_enabled())
            throw sat::solver_exception("sat solver does not support proofs");
        TRACE("before_sat_solver", s.display(tout););
        s.elim_redundancies();
        if (s.inconsistent()) {
            mc = 0;
            return;
        }
        
        atom2bool_var map(m);
        m_as2sat(s, m_params, m_solver, map);
        TRACE("sat_solver_unknown", tout << "interpreted_atoms: " << map.interpreted_atoms() << "\n";
              atom2bool_var::iterator it  = map.begin();
              atom2bool_var::iterator end = map.end();
              for (; it != end; ++it) {
                  if (!is_uninterp_const(it->m_key))
                      tout << mk_ismt2_pp(it->m_key, m) << "\n";
              });
        s.reset();
        s.m().compact_memory();
        CASSERT("sat_solver", m_solver.check_invariant());
        IF_VERBOSE(ST_VERBOSITY_LVL, m_solver.display_status(verbose_stream()););
        TRACE("sat_dimacs", m_solver.display_dimacs(tout););

        lbool r = m_solver.check();
        if (r == l_false) {
            mc = 0;
            s.reset();
            s.assert_expr(m.mk_false(), 0);
            return;
        }
        else if (r == l_true && !map.interpreted_atoms()) {
            // register model
            model_ref md = alloc(model, m);
            sat::model const & ll_m = m_solver.get_model();
            TRACE("sat_solver_strategy", for (unsigned i = 0; i < ll_m.size(); i++) tout << i << ":" << ll_m[i] << " "; tout << "\n";);
            atom2bool_var::iterator it  = map.begin();
            atom2bool_var::iterator end = map.end();
            for (; it != end; ++it) {
                expr * n   = it->m_key;
                sat::bool_var v = it->m_value;
                TRACE("sat_solver_strategy", tout << "extracting value of " << mk_ismt2_pp(n, m) << "\nvar: " << v << "\n";);
                switch (sat::value_at(v, ll_m)) {
                case l_true: 
                    md->register_decl(to_app(n)->get_decl(), m.mk_true()); 
                    break;
                case l_false:
                    md->register_decl(to_app(n)->get_decl(), m.mk_false());
                    break;
                default:
                    break;
                }
            }
            s.reset();
            TRACE("sat_solver_strategy", model_v2_pp(tout, *md););
            mc = model2model_converter(md.get());
        }
        else {
            // get simplified problem.
#if 0
            IF_VERBOSE(ST_VERBOSITY_LVL, verbose_stream() << "\"formula constains interpreted atoms, recovering formula from sat solver...\"\n";);
#endif
            m_solver.pop(m_solver.scope_lvl());
            m_sat2as(m_solver, map, m_params, s, mc);
        }
    }

    void set_cancel(bool f) {
        m_as2sat.set_cancel(f);
        m_sat2as.set_cancel(f);
        m_solver.set_cancel(f);
    }
};

sat_solver_strategy::sat_solver_strategy(ast_manager & m, params_ref const & p):
    m_imp(0),
    m_params(p) {
}

sat_solver_strategy::~sat_solver_strategy() {
    SASSERT(m_imp == 0);
}

void sat_solver_strategy::updt_params(params_ref const & p) {
    m_params = p;
}

void sat_solver_strategy::get_param_descrs(param_descrs & r) {
    assertion_set2sat::collect_param_descrs(r);
    sat2assertion_set::collect_param_descrs(r);
    sat::solver::collect_param_descrs(r);
    insert_produce_models(r);                                        
}


struct sat_solver_strategy::scoped_set_imp {
    sat_solver_strategy * m_owner; 
    scoped_set_imp(sat_solver_strategy * o, sat_solver_strategy::imp * i):m_owner(o) {
        #pragma omp critical (sat_solver_strategy)
        {
            m_owner->m_imp = i;
        }
    }

    ~scoped_set_imp() {
        #pragma omp critical (sat_solver_strategy)
        {
            m_owner->m_imp = 0;
        }
    }
};

void sat_solver_strategy::operator()(assertion_set & s, model_converter_ref & mc) {
    imp proc(s.m(), m_params);
    scoped_set_imp set(this, &proc);
    try {
        proc(s, mc);
        proc.m_solver.collect_statistics(m_stats);
    }
    catch (sat::solver_exception & ex) {
        proc.m_solver.collect_statistics(m_stats);
        throw ex;
    }
    TRACE("sat_stats", m_stats.display_smt2(tout););
}

void sat_solver_strategy::cleanup() {
    SASSERT(m_imp == 0);
}

void sat_solver_strategy::set_cancel(bool f) {
    #pragma omp critical (sat_solver_strategy)
    {
        if (m_imp)
            m_imp->set_cancel(f);
    }
}

void sat_solver_strategy::reset_statistics() {
    m_stats.reset();
}

void sat_solver_strategy::collect_statistics(statistics & st) const {
    st.copy(m_stats);
}
