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
#include "util/debug.h"
#include "ast/rewriter/rewriter_types.h"
#include "ast/ast_util.h"
#include "ast/ast_ll_pp.h"
#include "smt/smt_kernel.h"
#include "smt/params/smt_params.h"
#include "smt/params/smt_params_helper.hpp"
#include "smt/smt_solver.h"
#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "ast/converters/generic_model_converter.h"
#include "solver/solver2tactic.h"
#include "solver/solver.h"
#include "solver/mus.h"
#include "solver/parallel_tactical.h"
#include "solver/parallel_params.hpp"

typedef obj_map<expr, expr *> expr2expr_map;


class smt_tactic : public tactic {
    ast_manager&                 m;
    smt_params                   m_params;
    params_ref                   m_params_ref;
    expr_ref_vector              m_vars;
    vector<std::pair<expr_ref, expr_ref>> m_values;
    statistics                   m_stats;
    smt::kernel*                 m_ctx = nullptr;
    symbol                       m_logic;
    progress_callback*           m_callback = nullptr;
    bool                         m_candidate_models = false;
    bool                         m_fail_if_inconclusive = false;

public:
    smt_tactic(ast_manager& m, params_ref const & p):
        m(m),
        m_params_ref(p),
        m_vars(m) {
        updt_params_core(p);
        TRACE("smt_tactic", tout << "p: " << p << "\n";);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(smt_tactic, m, m_params_ref);
    }

    ~smt_tactic() override {
        SASSERT(m_ctx == nullptr);
    }

    char const* name() const override { return "smt"; }

    smt_params & fparams() {
        return m_params;
    }

    params_ref & params() {
        return m_params_ref;
    }

    void updt_params_core(params_ref const & p) {
        smt_params_helper _p(p);
        m_candidate_models     = _p.candidate_models();
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
        r.insert("fail_if_inconclusive", CPK_BOOL, "(default: true) fail if found unsat (sat) for under (over) approximated goal.");
        smt_params_helper::collect_param_descrs(r);
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
            m_params_ref.reset();
            m_params_ref.append(o.params());
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
            m_owner.m_user_ctx = nullptr;

            if (d)
                dealloc(d);
        }
    };

    void handle_canceled(goal_ref const & in,
                         goal_ref_buffer & result) {
    }

    void operator()(goal_ref const & in,
                    goal_ref_buffer & result) override {
        try {
            IF_VERBOSE(10, verbose_stream() << "(smt.tactic start)\n";);
            tactic_report report("smt", *in);
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
            SASSERT(m_ctx);

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
            user_propagate_delay_init();

            lbool r;
            try {
                if (assumptions.empty() && !m_user_ctx)
                    r = m_ctx->setup_and_check();
                else
                    r = m_ctx->check(assumptions.size(), assumptions.data());
            }
            catch(...) {
                TRACE("smt_tactic", tout << "exception\n";);
                m_ctx->collect_statistics(m_stats);
                throw;
            }
            SASSERT(m_ctx);
            m_ctx->collect_statistics(m_stats);
            proof_ref pr(m_ctx->get_proof(), m);
            TRACE("smt_tactic", tout << r << " " << pr << "\n";);
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
                    m_ctx->get_relevant_labels(nullptr, r);
                    labels_vec rv;
                    rv.append(r.size(), r.data());
                    model_converter_ref mc;
                    mc = model_and_labels2model_converter(md.get(), rv);
                    mc = concat(fmc.get(), mc.get());
                    in->add(mc.get());
                }
                if (m_ctx->canceled()) 
                    throw tactic_exception(Z3_CANCELED_MSG);                
                return;
            }
            case l_false: {
                if (m_fail_if_inconclusive && !in->unsat_preserved()) {
                    TRACE("smt_tactic", tout << "failed to show to be unsat...\n";);
                    throw tactic_exception("under-approximated goal found to be unsat");
                }
                // formula is unsat, reset the goal, and store false there.
                in->reset();
                expr_dependency * lcore = nullptr;
                if (in->unsat_core_enabled()) {
                    unsigned sz = m_ctx->get_unsat_core_size();
                    for (unsigned i = 0; i < sz; i++) {
                        expr * b = m_ctx->get_unsat_core_expr(i);
                        SASSERT(is_uninterp_const(b) && m.is_bool(b));
                        expr * d = bool2dep.find(b);
                        lcore = m.mk_join(lcore, m.mk_leaf(d));
                    }
                }

                if (m.proofs_enabled() && !pr) pr = m.mk_asserted(m.mk_false()); // bail out
                if (pr && m.get_fact(pr) != m.mk_false()) pr = m.mk_asserted(m.mk_false()); // could happen in clause_proof mode
                in->assert_expr(m.mk_false(), pr, lcore);
                
                result.push_back(in.get());
                return;
            }
            case l_undef:

                if (m_ctx->canceled() && !pr) {
                    throw tactic_exception(Z3_CANCELED_MSG);
                }

                if (m_fail_if_inconclusive && !m_candidate_models && !pr) {
                    std::stringstream strm;
                    strm << "smt tactic failed to show goal to be sat/unsat " << m_ctx->last_failure_as_string();
                    throw tactic_exception(strm.str());
                }
                result.push_back(in.get());
                if (pr) {
                    in->reset();
                    in->assert_expr(m.get_fact(pr), pr, nullptr);
                    in->updt_prec(goal::UNDER_OVER);
                }
                if (m_candidate_models) {
                    switch (m_ctx->last_failure()) {
                    case smt::NUM_CONFLICTS:
                    case smt::THEORY:
                    case smt::QUANTIFIERS:
                        if (in->models_enabled()) {
                            model_ref md;
                            m_ctx->get_model(md);
                            buffer<symbol> r;
                            m_ctx->get_relevant_labels(nullptr, r);
                            labels_vec rv;
                            rv.append(r.size(), r.data());
                            in->add(model_and_labels2model_converter(md.get(), rv));
                        }
                        return;
                    default:
                        break;
                    }
                }
                if (pr) {
                    return;
                }
                throw tactic_exception(m_ctx->last_failure_as_string());
            }
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.what());
        }
    }

    void* m_user_ctx = nullptr;
    user_propagator::push_eh_t  m_push_eh;
    user_propagator::pop_eh_t   m_pop_eh;
    user_propagator::fresh_eh_t m_fresh_eh;
    user_propagator::fixed_eh_t m_fixed_eh;
    user_propagator::final_eh_t m_final_eh;
    user_propagator::eq_eh_t    m_eq_eh;
    user_propagator::eq_eh_t    m_diseq_eh;
    user_propagator::created_eh_t m_created_eh;
    user_propagator::decide_eh_t m_decide_eh;
    void* m_on_clause_ctx = nullptr;
    user_propagator::on_clause_eh_t m_on_clause_eh;

    void on_clause_delay_init() {
        if (m_on_clause_eh)
            m_ctx->register_on_clause(m_on_clause_ctx, m_on_clause_eh);
    }

    void user_propagate_delay_init() {
        if (!m_user_ctx)
            return;
        m_ctx->user_propagate_init(m_user_ctx, m_push_eh, m_pop_eh, m_fresh_eh);
        if (m_fixed_eh)   m_ctx->user_propagate_register_fixed(m_fixed_eh);
        if (m_final_eh)   m_ctx->user_propagate_register_final(m_final_eh);
        if (m_eq_eh)      m_ctx->user_propagate_register_eq(m_eq_eh);
        if (m_diseq_eh)   m_ctx->user_propagate_register_diseq(m_diseq_eh);
        if (m_created_eh) m_ctx->user_propagate_register_created(m_created_eh);
        if (m_decide_eh) m_ctx->user_propagate_register_decide(m_decide_eh);

        for (expr* v : m_vars) 
            m_ctx->user_propagate_register_expr(v);
        for (auto& [var, value] : m_values)
            m_ctx->user_propagate_initialize_value(var, value);
    }

    void user_propagate_clear() override {
        m_user_ctx = nullptr;
        m_vars.reset();
        m_fixed_eh = nullptr;
        m_final_eh = nullptr;
        m_eq_eh = nullptr;
        m_diseq_eh = nullptr;
        m_created_eh = nullptr;
        m_decide_eh = nullptr;
        m_on_clause_eh = nullptr;
        m_on_clause_ctx = nullptr;
    }

    void register_on_clause(void* ctx, user_propagator::on_clause_eh_t& on_clause) override {
        m_on_clause_ctx = ctx;
        m_on_clause_eh = on_clause;
    }

    void user_propagate_init(
        void* ctx,
        user_propagator::push_eh_t& push_eh,
        user_propagator::pop_eh_t& pop_eh,
        user_propagator::fresh_eh_t& fresh_eh) override {
        user_propagate_clear();
        m_user_ctx = ctx;
        m_push_eh = push_eh;
        m_pop_eh = pop_eh;
        m_fresh_eh = fresh_eh;
    }

    void user_propagate_register_fixed(user_propagator::fixed_eh_t& fixed_eh) override {
        m_fixed_eh = fixed_eh;
    }

    void user_propagate_register_final(user_propagator::final_eh_t& final_eh) override {
        m_final_eh = final_eh;
    }

    void user_propagate_register_eq(user_propagator::eq_eh_t& eq_eh) override {
        m_eq_eh = eq_eh;
    }

    void user_propagate_register_diseq(user_propagator::eq_eh_t& diseq_eh) override {
        m_diseq_eh = diseq_eh;
    }

    void user_propagate_register_expr(expr* e) override {
        m_vars.push_back(e);
    }

    void user_propagate_register_created(user_propagator::created_eh_t& created_eh) override {
        m_created_eh = created_eh;
    }
    
    void user_propagate_register_decide(user_propagator::decide_eh_t& decide_eh) override {
        m_decide_eh = decide_eh;
    }

    void user_propagate_initialize_value(expr* var, expr* value) override {
        m_values.push_back({expr_ref(var, m), expr_ref(value, m)});
    }
};

static tactic * mk_seq_smt_tactic(ast_manager& m, params_ref const & p) {
    return alloc(smt_tactic, m, p);
}


tactic * mk_parallel_smt_tactic(ast_manager& m, params_ref const& p) {
    return mk_parallel_tactic(mk_smt_solver(m, p, symbol::null), p);
}

tactic * mk_smt_tactic_core(ast_manager& m, params_ref const& p, symbol const& logic) {
    parallel_params pp(p);
    return pp.enable() ? mk_parallel_tactic(mk_smt_solver(m, p, logic), p) : mk_seq_smt_tactic(m, p);
}

tactic * mk_smt_tactic_core_using(ast_manager& m, bool auto_config, params_ref const& _p) {
    parallel_params pp(_p);
    params_ref p = _p;
    p.set_bool("auto_config", auto_config);
    return using_params(pp.enable() ? mk_parallel_smt_tactic(m, p) : mk_seq_smt_tactic(m, p), p);
}

