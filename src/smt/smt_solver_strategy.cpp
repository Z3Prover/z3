/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_solver_strategy.cpp

Abstract:

    Wraps a solver as an assertion_set strategy.
    **Temporary code**
    It should be deleted when we finish porting the assertion_set code to the tactic framework.

Author:

    Leonardo (leonardo) 2012-10-20

Notes:

--*/
#include"smt_solver_strategy.h"
#include"smt_solver.h"
#include"front_end_params.h"
#include"params2front_end_params.h"

class as_st_solver : public assertion_set_strategy {
    scoped_ptr<front_end_params> m_params;
    params_ref                   m_params_ref;
    statistics                   m_stats;
    std::string                  m_failure;
    smt::solver *                m_ctx;
    bool                         m_candidate_models;
    symbol                       m_logic;
    progress_callback *          m_callback;
public:
    as_st_solver(bool candidate_models):m_ctx(0), m_candidate_models(candidate_models), m_callback(0) {}
    
    front_end_params & fparams() {
        if (!m_params)
            m_params = alloc(front_end_params);
        return *m_params;
    }

    struct scoped_init_ctx {
        as_st_solver & m_owner;

        scoped_init_ctx(as_st_solver & o, ast_manager & m):m_owner(o) {
            smt::solver * new_ctx = alloc(smt::solver, m, o.fparams());
            TRACE("as_solver", tout << "logic: " << o.m_logic << "\n";);
            new_ctx->set_logic(o.m_logic);
            if (o.m_callback) {
                new_ctx->set_progress_callback(o.m_callback);
            }
            #pragma omp critical (as_st_solver) 
            {
                o.m_ctx = new_ctx;
            }
        }

        ~scoped_init_ctx() {
            smt::solver * d = m_owner.m_ctx;
            #pragma omp critical (as_st_cancel)
            {
                m_owner.m_ctx = 0;
            }
            if (d)
                dealloc(d);
        }
    };

    virtual ~as_st_solver() {
        SASSERT(m_ctx == 0);
    }

    virtual void updt_params(params_ref const & p) {
        TRACE("as_solver", tout << "updt_params: " << p << "\n";);
        m_params_ref = p;
        params2front_end_params(m_params_ref, fparams());
    }

    virtual void collect_param_descrs(param_descrs & r) {
    }

    virtual void set_cancel(bool f) {
        if (m_ctx)
            m_ctx->set_cancel(f);
    }

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        SASSERT(is_well_sorted(s));
        IF_VERBOSE(ST_VERBOSITY_LVL, verbose_stream() << "(smt-solver)" << std::endl;);
        TRACE("as_solver", tout << "AUTO_CONFIG: " << fparams().m_auto_config << " HIDIV0: " << fparams().m_hi_div0 << " " 
              << " PREPROCESS: " << fparams().m_preprocess << ", SOLVER:" << fparams().m_solver << "\n";);
        TRACE("as_solver_detail", s.display(tout););        
        ast_manager & m = s.m();
        TRACE("as_solver_memory", tout << "wasted_size: " << m.get_allocator().get_wasted_size() << "\n";);        
        // verbose_stream() << "wasted_size: " << m.get_allocator().get_wasted_size() << ", free_objs: " << m.get_allocator().get_num_free_objs() << "\n";
        // m.get_allocator().consolidate();        
        scoped_init_ctx  init(*this, m);
        SASSERT(m_ctx != 0);
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * f = s.form(i);
            m_ctx->assert_expr(f);
        }
        lbool r = m_ctx->setup_and_check();
        m_ctx->collect_statistics(m_stats);
        switch (r) {
        case l_true: {
            // the empty assertion set is trivially satifiable.
            s.reset(); 
            // store the model in a do nothin model converter.
            model_ref md;
            m_ctx->get_model(md);
            mc = model2model_converter(md.get());
            return;
        }
        case l_false:
            // formula is unsat, reset the assertion set, and store false there.
            s.reset();
            s.assert_expr(m.mk_false(), m_ctx->get_proof());
            return;
        case l_undef:
            if (m_candidate_models) {
                switch (m_ctx->last_failure()) {
                case smt::NUM_CONFLICTS:
                case smt::THEORY:
                case smt::QUANTIFIERS: {
                    model_ref md;
                    m_ctx->get_model(md);
                    mc = model2model_converter(md.get());
                    return;
                }
                default:
                    break;
                }
            }
            m_failure = m_ctx->last_failure_as_string();
            throw strategy_exception(m_failure.c_str());
        }
    }

    virtual void collect_statistics(statistics & st) const {
        if (m_ctx)
            m_ctx->collect_statistics(st); // ctx is still running...
        else
            st.copy(m_stats);
    }

    virtual void cleanup() {
    }

    virtual void reset_statistics() {
        m_stats.reset();
    }
    
    // for backward compatibility
    virtual void set_front_end_params(front_end_params & p) {
        m_params = alloc(front_end_params, p);
        // must propagate the params_ref to fparams
        params2front_end_params(m_params_ref, fparams());
    }

    virtual void set_logic(symbol const & l) {
        m_logic = l;
    }

    virtual void set_progress_callback(progress_callback * callback) {
        m_callback = callback;
    }
};

as_st * mk_smt_solver_core(bool candidate_models) {
    return alloc(as_st_solver, candidate_models);
}

as_st * mk_smt_solver(bool auto_config, bool candidate_models) {
    as_st * solver = mk_smt_solver_core(candidate_models);
    params_ref solver_p;    
    solver_p.set_bool(":auto-config", auto_config);
    return using_params(solver, solver_p);
};
