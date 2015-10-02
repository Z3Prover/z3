/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt_tactic.h

Abstract:

    smt::context as a tactic.

Author:

    Leonardo (leonardo) 2011-10-18

Notes:

--*/
#include"tactic.h"
#include"tactical.h"
#include"smt_kernel.h"
#include"smt_params.h"
#include"smt_params_helper.hpp"
#include"rewriter_types.h"
#include"filter_model_converter.h"
#include"ast_util.h"

typedef obj_map<expr, expr *> expr2expr_map;

void extract_clauses_and_dependencies(goal_ref const& g, expr_ref_vector& clauses, ptr_vector<expr>& assumptions, expr2expr_map& bool2dep, ref<filter_model_converter>& fmc) {
    expr2expr_map dep2bool;
    ptr_vector<expr> deps;
    ast_manager& m = g->m();
    expr_ref_vector clause(m);
    unsigned sz = g->size();
    for (unsigned i = 0; i < sz; i++) {
        expr * f            = g->form(i);
        expr_dependency * d = g->dep(i);
        if (d == 0 || !g->unsat_core_enabled()) {
            clauses.push_back(f);
        }
        else {
            // create clause (not d1 \/ ... \/ not dn \/ f) when the d's are the assumptions/dependencies of f.
            clause.reset();
            clause.push_back(f);
            deps.reset();
            m.linearize(d, deps);
            SASSERT(!deps.empty()); // d != 0, then deps must not be empty
            ptr_vector<expr>::iterator it  = deps.begin();
            ptr_vector<expr>::iterator end = deps.end();
            for (; it != end; ++it) {
                expr * d = *it;
                if (is_uninterp_const(d) && m.is_bool(d)) {
                    // no need to create a fresh boolean variable for d
                    if (!bool2dep.contains(d)) {
                        assumptions.push_back(d);
                        bool2dep.insert(d, d);
                    }
                    clause.push_back(m.mk_not(d));
                }
                else {
                    // must normalize assumption 
                    expr * b = 0;
                    if (!dep2bool.find(d, b)) {
                        b = m.mk_fresh_const(0, m.mk_bool_sort());
                        dep2bool.insert(d, b);
                        bool2dep.insert(b, d);
                        assumptions.push_back(b);
                        if (!fmc) {
                            fmc = alloc(filter_model_converter, m);
                        }
                        fmc->insert(to_app(b)->get_decl());
                    }
                    clause.push_back(m.mk_not(b));
                }
            }
            SASSERT(clause.size() > 1);
            expr_ref cls(m);
            cls = mk_or(m, clause.size(), clause.c_ptr());
            clauses.push_back(cls);
        }
    }    
}

class smt_tactic : public tactic {
    smt_params                   m_params;
    params_ref                   m_params_ref;
    statistics                   m_stats;
    std::string                  m_failure;
    smt::kernel *                m_ctx;
    symbol                       m_logic;
    progress_callback *          m_callback;
    bool                         m_candidate_models;
    bool                         m_fail_if_inconclusive;

public:
    smt_tactic(params_ref const & p):
        m_params_ref(p),
        m_ctx(0), 
        m_callback(0) {
        updt_params_core(p);
        TRACE("smt_tactic", tout << this << "\np: " << p << "\n";);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(smt_tactic, m_params_ref);
    }

    virtual ~smt_tactic() {
        SASSERT(m_ctx == 0);
    }

    smt_params & fparams() {
        return m_params;
    }

    void updt_params_core(params_ref const & p) {
        m_candidate_models     = p.get_bool("candidate_models", false);
        m_fail_if_inconclusive = p.get_bool("fail_if_inconclusive", true);
    }
    
    virtual void updt_params(params_ref const & p) {
        TRACE("smt_tactic", tout << this << "\nupdt_params: " << p << "\n";);
        updt_params_core(p);
        fparams().updt_params(p);
        SASSERT(p.get_bool("auto_config", fparams().m_auto_config) == fparams().m_auto_config);
    }
    
    virtual void collect_param_descrs(param_descrs & r) {
        r.insert("candidate_models", CPK_BOOL, "(default: false) create candidate models even when quantifier or theory reasoning is incomplete.");
        r.insert("fail_if_inconclusive", CPK_BOOL, "(default: true) fail if found unsat (sat) for under (over) approximated goal.");
        smt_params_helper::collect_param_descrs(r);
    }
    
    virtual void set_cancel(bool f) {
        if (m_ctx)
            m_ctx->set_cancel(f);
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
    
    virtual void set_logic(symbol const & l) {
        m_logic = l;
    }

    virtual void set_progress_callback(progress_callback * callback) {
        m_callback = callback;
    }
    
    struct scoped_init_ctx {
        smt_tactic & m_owner;
        smt_params   m_params; // smt-setup overwrites parameters depending on the current assertions.

        scoped_init_ctx(smt_tactic & o, ast_manager & m):m_owner(o) {
            m_params = o.fparams();
            smt::kernel * new_ctx = alloc(smt::kernel, m, m_params);
            TRACE("smt_tactic", tout << "logic: " << o.m_logic << "\n";);
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
            smt::kernel * d = m_owner.m_ctx;
            #pragma omp critical (as_st_cancel)
            {
                m_owner.m_ctx = 0;
            }
            if (d)
                dealloc(d);
        }
    };


    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        try {
            SASSERT(in->is_well_sorted());
            ast_manager & m = in->m();
            TRACE("smt_tactic", tout << this << "\nAUTO_CONFIG: " << fparams().m_auto_config << " HIDIV0: " << fparams().m_hi_div0 << " " 
                  << " PREPROCESS: " << fparams().m_preprocess << "\n";
                  tout << "RELEVANCY: " << fparams().m_relevancy_lvl << "\n";
                  tout << "fail-if-inconclusive: " << m_fail_if_inconclusive << "\n";
                  tout << "params_ref: " << m_params_ref << "\n";
                  tout << "nnf: " << fparams().m_nnf_cnf << "\n";);
            TRACE("smt_tactic_detail", in->display(tout););
            TRACE("smt_tactic_memory", tout << "wasted_size: " << m.get_allocator().get_wasted_size() << "\n";);        
            scoped_init_ctx  init(*this, m);
            SASSERT(m_ctx != 0);

            expr_ref_vector clauses(m);
            expr2expr_map               bool2dep; 
            ptr_vector<expr>            assumptions;       
            ref<filter_model_converter> fmc;
            if (in->unsat_core_enabled()) {
                extract_clauses_and_dependencies(in, clauses, assumptions, bool2dep, fmc);
                if (in->proofs_enabled() && !assumptions.empty())
                    throw tactic_exception("smt tactic does not support simultaneous generation of proofs and unsat cores");
                for (unsigned i = 0; i < clauses.size(); ++i) {
                    m_ctx->assert_expr(clauses[i].get());
                }
            }
            else if (in->proofs_enabled()) {
                unsigned sz = in->size();
                for (unsigned i = 0; i < sz; i++) {
                    m_ctx->assert_expr(in->form(i), in->pr(i));
                }
            }
            else {
                unsigned sz = in->size();
                for (unsigned i = 0; i < sz; i++) {
                    m_ctx->assert_expr(in->form(i));
                }
            }
            if (m_ctx->canceled()) {
                throw tactic_exception("smt_tactic canceled");
            }
            
            lbool r;
            if (assumptions.empty())
                r = m_ctx->setup_and_check();
            else
                r = m_ctx->check(assumptions.size(), assumptions.c_ptr());
            m_ctx->collect_statistics(m_stats);
            switch (r) {
            case l_true: {
                if (m_fail_if_inconclusive && !in->sat_preserved())
                    throw tactic_exception("over-approximated goal found to be sat");
                // the empty assertion set is trivially satifiable.
                in->reset();
                result.push_back(in.get());
                // store the model in a no-op model converter, and filter fresh Booleans
                if (in->models_enabled()) {
                    model_ref md;
                    m_ctx->get_model(md);
                    mc = model2model_converter(md.get());
                    mc = concat(fmc.get(), mc.get());
                }
                pc = 0;
                core = 0;
                return;
            }
            case l_false: {
                if (m_fail_if_inconclusive && !in->unsat_preserved()) {
                    TRACE("smt_tactic", tout << "failed to show to be unsat...\n";);
                    throw tactic_exception("under-approximated goal found to be unsat");
                }
                // formula is unsat, reset the goal, and store false there.
                in->reset();
                proof * pr              = 0;
                expr_dependency * lcore = 0;
                if (in->proofs_enabled())
                    pr = m_ctx->get_proof();
                if (in->unsat_core_enabled()) {
                    unsigned sz = m_ctx->get_unsat_core_size();
                    for (unsigned i = 0; i < sz; i++) {
                        expr * b = m_ctx->get_unsat_core_expr(i);
                        SASSERT(is_uninterp_const(b) && m.is_bool(b));
                        expr * d = bool2dep.find(b);
                        lcore = m.mk_join(lcore, m.mk_leaf(d));
                    }
                }
                in->assert_expr(m.mk_false(), pr, lcore);
                result.push_back(in.get());
                mc   = 0;
                pc   = 0;
                core = 0;
                return;
            }
            case l_undef:
                if (m_fail_if_inconclusive)
                    throw tactic_exception("smt tactic failed to show goal to be sat/unsat");
                result.push_back(in.get());
                if (m_candidate_models) {
                    switch (m_ctx->last_failure()) {
                    case smt::NUM_CONFLICTS:
                    case smt::THEORY:
                    case smt::QUANTIFIERS:
                        if (in->models_enabled()) {
                            model_ref md;
                            m_ctx->get_model(md);
                            mc = model2model_converter(md.get());
                        }
                        pc   = 0;
                        core = 0;
                        return;
                    default:
                        break;
                    }
                }
                m_failure = m_ctx->last_failure_as_string();
                throw tactic_exception(m_failure.c_str());
            }
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }
};

tactic * mk_smt_tactic(params_ref const & p) {
    return alloc(smt_tactic, p);
}

tactic * mk_smt_tactic_using(bool auto_config, params_ref const & _p) {
    params_ref p = _p;    
    p.set_bool("auto_config", auto_config);
    tactic * r = mk_smt_tactic(p);
    TRACE("smt_tactic", tout << "auto_config: " << auto_config << "\nr: " << r << "\np: " << p << "\n";);
    return using_params(r, p);
}

