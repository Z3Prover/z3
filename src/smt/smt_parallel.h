/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_parallel.h

Abstract:

    Parallel SMT, portfolio loop specialized to SMT core.

Author:

    nbjorner 2020-01-31

Revision History:

--*/
#pragma once

#include "smt/smt_context.h"

namespace smt {

    class parallel {
        context& ctx;

        class worker {
            ast_manager m;
            context ctx;
            expr_ref_vector asms;
        public:
            worker(context& ctx, expr_ref_vector const& asms);
            void run();
            void cancel();
        };

        std::mutex mux;
        void set_unsat();
        void set_sat(ast_translation& tr, model& m);
        void get_cubes(ast_translation& tr, expr_ref_vector& cubes);

    public:
        parallel(context& ctx): ctx(ctx) {}

        lbool operator()(expr_ref_vector const& asms);

    };

}
