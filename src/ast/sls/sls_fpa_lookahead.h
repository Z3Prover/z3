/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    sls_fpa_lookahead.h

Abstract:

    Local GPU-emulator for floating-point SLS lookahead.

Author:

    Atomic

--*/
#pragma once

#include <functional>
#include "ast/sls/sls_context.h"

namespace sls {

    struct fpa_lookahead_candidate {
        ptr_vector<expr> vars;
        ptr_vector<expr> values;
    };

    class fpa_gpu_emulator {
        struct config {
            bool initialized = false;
            symbol mode = symbol("auto");
            bool use_callback = true;
        };

        context& m_ctx;
        mutable config m_config;
        mutable unsigned m_callback_calls = 0;
        mutable unsigned m_emulator_calls = 0;

        void updt_params(params_ref const& p) const;
        void serialize_rec(expr* e, expr_mark& visited, ptr_vector<expr>& dag) const;
    public:
        explicit fpa_gpu_emulator(context& ctx): m_ctx(ctx) {}

        void serialize_dag(expr* atom, ptr_vector<expr>& dag) const;

        int choose_candidate(
            expr* atom,
            bool desired,
            ptr_vector<expr> const& dag,
            vector<fpa_lookahead_candidate> const& candidates,
            std::function<bool(fpa_lookahead_candidate const&)> const& accept) const;

        void collect_statistics(statistics& st) const;
    };

}
