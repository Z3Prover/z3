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

namespace sls {

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
        TRACE(sls, tout << "fpa-lookahead atom=" << mk_bounded_pp(atom, m_ctx.get_manager())
                        << " desired=" << desired
                        << " dag=" << dag.size()
                        << " candidates=" << candidates.size() << "\n";);

        ptr_vector<expr> vars;
        ptr_vector<expr> values;
        unsigned num_candidates = candidates.size();
        if (!candidates.empty()) {
            for (expr* v : candidates[0].vars)
                vars.push_back(v);
            for (auto const& c : candidates)
                for (expr* v : c.values)
                    values.push_back(v);

            int idx = m_ctx.eval_fpa_candidates(atom, desired, dag, vars, values, num_candidates);
            if (0 <= idx && static_cast<unsigned>(idx) < candidates.size() && accept(candidates[idx]))
                return idx;
        }

        for (unsigned i = 0; i < candidates.size(); ++i) {
            if (accept(candidates[i]))
                return static_cast<int>(i);
        }
        return -1;
    }

}
