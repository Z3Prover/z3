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
#include "util/lp/lp_params.hpp"
#include "ast/rewriter/rewriter_types.h"
#include "ast/ast_util.h"
#include "smt/smt_kernel.h"
#include "smt/params/smt_params.h"
#include "smt/params/smt_params_helper.hpp"
#include "smt/smt_solver.h"
#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "tactic/generic_model_converter.h"
#include "solver/solver2tactic.h"
#include "solver/solver.h"
#include "solver/mus.h"
#include "solver/parallel_tactic.h"
#include "solver/parallel_params.hpp"

typedef obj_map<expr, expr *> expr2expr_map;


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
        m_ctx(nullptr),
        m_callback(nullptr) {
        updt_params_core(p);
        TRACE("smt_tactic", tout << "p: " << p << "\n";);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(smt_tactic, m_params_ref);
    }

    ~smt_tactic() override {
        SASSERT(m_ctx == 0);
    }

    smt_params & fparams() {
        return m_params;
    }

    params_ref & params() {
        return m_params_ref;
    }

    void updt_params_core(params_ref const & p) {
        m_candidate_models     = p.get_bool("candidate_models", false);
        m_fail_if_inconclusive = p.get_bool("fail_if_inconclusive", true);
    }

    void updt_params(params_ref const & p) override {
        TRACE("smt_tactic", tout << "updt_params: " << p << "\n";);
        updt_params_core(p);
        fparams().updt_params(p);
        m_params_ref.copy(p);
        m_logic = p.get_sym(symbol("logic"), m_logic);
        if (m_logic != symbol::null && m_ctx) {
            m_ctx->set_logic(m_logic);
        }
        SASSERT(p.get_bool("auto_config", fparams().m_auto_config) == fparams().m_auto_config);
    }

    void collect_param_descrs(param_descrs & r) override {
        r.insert("candidate_models", CPK_BOOL, "(default: false) create candidate models even when quantifier or theory reasoning is incomplete.");
        r.insert("fail_if_inconclusive", CPK_BOOL, "(default: true) fail if found unsat (sat) for under (over) approximated goal.");
        smt_params_helper::collect_param_descrs(r);
        lp_params::collect_param_descrs(r);
    }


    void collect_statistics(statistics & st) const override {
        if (m_ctx)
            m_ctx->collect_statistics(st); // ctx is still running...
        else
            st.copy(m_stats);
    }

    void cleanup() override {
    }

    void reset_statistics() override {
        m_stats.reset();
    }

    void set_logic(symbol const & l) override {
        m_logic = l;
    }

    void set_progress_callback(progress_callback * callback) override {
        m_callback = callback;
    }

    struct scoped_init_ctx {
        smt_tactic & m_owner;
        smt_params   m_params; // smt-setup overwrites parameters depending on the current assertions.
        params_ref   m_params_ref;

        scoped_init_ctx(smt_tactic & o, ast_manager & m):m_owner(o) {
            m_params = o.fparams();
            m_params_ref = o.params();
            smt::kernel * new_ctx = alloc(smt::kernel, m, m_params, m_params_ref);
            TRACE("smt_tactic", tout << "logic: " << o.m_logic << "\n";);
            new_ctx->set_logic(o.m_logic);
            if (o.m_callback) {
                new_ctx->set_progress_callback(o.m_callback);
            }
            o.m_ctx = new_ctx;

        }

        ~scoped_init_ctx() {
            smt::kernel * d = m_owner.m_ctx;
            m_owner.m_ctx = nullptr;

            if (d)
                dealloc(d);
        }
    };


    void operator()(goal_ref const & in,
                    goal_ref_buffer & result) override {
        try {
            IF_VERBOSE(10, verbose_stream() << "(smt.tactic start)\n";);
            SASSERT(in->is_well_sorted());
            ast_manager & m = in->m();
            TRACE("smt_tactic", tout << this << "\nAUTO_CONFIG: " << fparams().m_auto_config << " HIDIV0: " << fparams().m_hi_div0 << " "
                  << " PREPROCESS: " << fparams().m_preprocess << "\n";
                  tout << "RELEVANCY: " << fparams().m_relevancy_lvl << "\n";
                  tout << "fail-if-inconclusive: " << m_fail_if_inconclusive << "\n";
                  tout << "params_ref: " << m_params_ref << "\n";
                  tout << "nnf: " << fparams().m_nnf_cnf << "\n";);
            TRACE("smt_tactic_params", m_params.display(tout););
            TRACE("smt_tactic_detail", in->display(tout););
            TRACE("smt_tactic_memory", tout << "wasted_size: " << m.get_allocator().get_wasted_size() << "\n";);
            scoped_init_ctx  init(*this, m);
            SASSERT(m_ctx != 0);

            expr_ref_vector clauses(m);
            expr2expr_map               bool2dep;
            ptr_vector<expr>            assumptions;
            ref<generic_model_converter> fmc;
            if (in->unsat_core_enabled()) {
                extract_clauses_and_dependencies(in, clauses, assumptions, bool2dep, fmc);
                TRACE("mus", in->display_with_dependencies(tout);
                      tout << clauses << "\n";);
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
                throw tactic_exception(Z3_CANCELED_MSG);
            }

            lbool r;
            try {
                if (assumptions.empty())
                    r = m_ctx->setup_and_check();
                else
                    r = m_ctx->check(assumptions.size(), assumptions.c_ptr());
            }
            catch(...) {
                m_ctx->collect_statistics(m_stats);
                throw;
            }
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
                    buffer<symbol> r;
                    m_ctx->get_relevant_labels(0, r);
                    labels_vec rv;
                    rv.append(r.size(), r.c_ptr());
                    model_converter_ref mc;
                    mc = model_and_labels2model_converter(md.get(), rv);
                    mc = concat(fmc.get(), mc.get());
                    in->add(mc.get());
                }
                return;
            }
            case l_false: {
                if (m_fail_if_inconclusive && !in->unsat_preserved()) {
                    TRACE("smt_tactic", tout << "failed to show to be unsat...\n";);
                    throw tactic_exception("under-approximated goal found to be unsat");
                }
                // formula is unsat, reset the goal, and store false there.
                in->reset();
                proof * pr              = nullptr;
                expr_dependency * lcore = nullptr;
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
                return;
            }
            case l_undef:
                if (m_ctx->canceled()) {
                    throw tactic_exception(Z3_CANCELED_MSG);
                }
                if (m_fail_if_inconclusive && !m_candidate_models) {
                    std::stringstream strm;
                    strm << "smt tactic failed to show goal to be sat/unsat " << m_ctx->last_failure_as_string();
                    throw tactic_exception(strm.str().c_str());
                }
                result.push_back(in.get());
                if (m_candidate_models) {
                    switch (m_ctx->last_failure()) {
                    case smt::NUM_CONFLICTS:
                    case smt::THEORY:
                    case smt::QUANTIFIERS:
                        if (in->models_enabled()) {
                            model_ref md;
                            m_ctx->get_model(md);
                            buffer<symbol> r;
                            m_ctx->get_relevant_labels(0, r);
                            labels_vec rv;
                            rv.append(r.size(), r.c_ptr());
                            in->add(model_and_labels2model_converter(md.get(), rv));
                        }
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

tactic * mk_psmt_tactic(ast_manager& m, params_ref const& p, symbol const& logic) {
    parallel_params pp(p);
    return pp.enable() ? mk_parallel_tactic(mk_smt_solver(m, p, logic), p) : mk_smt_tactic(p);
}

tactic * mk_psmt_tactic_using(ast_manager& m, bool auto_config, params_ref const& _p, symbol const& logic) {
    parallel_params pp(_p);
    params_ref p = _p;
    p.set_bool("auto_config", auto_config);
    return using_params(pp.enable() ? mk_parallel_tactic(mk_smt_solver(m, p, logic), p) : mk_smt_tactic(p), p);
}

tactic * mk_parallel_smt_tactic(ast_manager& m, params_ref const& p) {
    return mk_parallel_tactic(mk_smt_solver(m, p, symbol::null), p);
}
