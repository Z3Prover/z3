/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    sls_fpa_lookahead.cpp

Abstract:

    Local GPU-emulator for floating-point SLS lookahead.

Author:

    Atomic

--*/
#include "ast/sls/sls_fpa_lookahead.h"
#include "params/sls_params.hpp"

namespace sls {

    void fpa_gpu_emulator::updt_params(params_ref const& p) const {
        if (m_config.initialized)
            return;
        sls_params sp(p);
        m_config.mode = sp.fp_mode();
        m_config.use_callback = sp.fp_use_callback();
        m_config.initialized = true;
    }

    void fpa_gpu_emulator::serialize_rec(expr* e, expr_mark& visited, ptr_vector<expr>& dag) const {
        if (visited.is_marked(e))
            return;
        visited.mark(e);
        if (is_app(e)) {
            for (expr* arg : *to_app(e))
                serialize_rec(arg, visited, dag);
        }
        dag.push_back(e);
    }

    void fpa_gpu_emulator::serialize_dag(expr* atom, ptr_vector<expr>& dag) const {
        dag.reset();
        expr_mark visited;
        serialize_rec(atom, visited, dag);
    }

    int fpa_gpu_emulator::choose_candidate(
        expr* atom,
        bool desired,
        ptr_vector<expr> const& dag,
        vector<fpa_lookahead_candidate> const& candidates,
        std::function<bool(fpa_lookahead_candidate const&)> const& accept) const {
        updt_params(m_ctx.get_params());
        TRACE(sls, tout << "fpa-lookahead atom=" << mk_bounded_pp(atom, m_ctx.get_manager())
                        << " desired=" << desired
                        << " dag=" << dag.size()
                        << " candidates=" << candidates.size()
                        << " mode=" << m_config.mode << " callback=" << m_config.use_callback << "\n";);

        ptr_vector<expr> vars;
        ptr_vector<expr> values;
        unsigned num_candidates = candidates.size();
        bool allow_callback = m_config.use_callback && m_config.mode != symbol("cpu");
        if (allow_callback && !candidates.empty()) {
            for (expr* v : candidates[0].vars)
                vars.push_back(v);
            for (auto const& c : candidates)
                for (expr* v : c.values)
                    values.push_back(v);

            int idx = m_ctx.eval_fpa_candidates(atom, desired, dag, vars, values, num_candidates);
            ++m_callback_calls;
            if (0 <= idx && static_cast<unsigned>(idx) < candidates.size() && accept(candidates[idx]))
                return idx;
        }

        for (unsigned i = 0; i < candidates.size(); ++i) {
            if (accept(candidates[i])) {
                ++m_emulator_calls;
                return static_cast<int>(i);
            }
        }
        return -1;
    }

    void fpa_gpu_emulator::collect_statistics(statistics& st) const {
        st.update("sls-fpa-callback-calls", m_callback_calls);
        st.update("sls-fpa-emulator-calls", m_emulator_calls);
    }

}
