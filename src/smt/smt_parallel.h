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
#include <thread>

namespace smt {

    class parallel {
        context& ctx;
        unsigned num_threads;

        class batch_manager {        

            enum state {
                is_running,
                is_sat,
                is_unsat,
                is_exception_msg,
                is_exception_code
            };

            ast_manager& m;
            parallel& p;
            std::mutex mux;
            state m_state = state::is_running;
            expr_ref_vector m_split_atoms; // atoms to split on
            vector<expr_ref_vector> m_cubes;
            unsigned m_max_batch_size = 10;
            unsigned m_exception_code = 0;
            std::string m_exception_msg;

            // called from batch manager to cancel other workers if we've reached a verdict
            void cancel_workers() {
                IF_VERBOSE(0, verbose_stream() << "Canceling workers\n");
                for (auto& w : p.m_workers) 
                    w->cancel();                
            }

        public:
            batch_manager(ast_manager& m, parallel& p) : m(m), p(p), m_split_atoms(m) { }

            void initialize();

            void set_unsat(ast_translation& l2g, expr_ref_vector const& unsat_core);
            void set_sat(ast_translation& l2g, model& m);
            void set_exception(std::string const& msg);
            void set_exception(unsigned error_code);

            //
            // worker threads ask the batch manager for a supply of cubes to check.
            // they pass in a translation function from the global context to local context (ast-manager). It is called g2l.
            // The batch manager returns a list of cubes to solve.
            //
            void get_cubes(ast_translation& g2l, vector<expr_ref_vector>& cubes);

            //
            // worker threads return unprocessed cubes to the batch manager together with split literal candidates.
            // the batch manager re-enqueues unprocessed cubes and optionally splits them using the split_atoms returned by this and workers.
            // 
            void return_cubes(ast_translation& l2g, vector<expr_ref_vector>const& cubes, expr_ref_vector const& split_atoms);
            void share_lemma(ast_translation& l2g, expr* lemma);
            lbool get_result() const;
        };

        class worker {
            unsigned id; // unique identifier for the worker
            parallel& p;
            batch_manager& b;
            ast_manager m;
            expr_ref_vector asms;
            smt_params m_smt_params;
            scoped_ptr<context> ctx;
            unsigned m_max_conflicts = 100;
            unsigned m_num_shared_units = 0;
            void share_units();
            lbool check_cube(expr_ref_vector const& cube);
        public:
            worker(unsigned id, parallel& p, expr_ref_vector const& _asms);
            void run();
            expr_ref_vector get_split_atoms();
            void cancel() {
                IF_VERBOSE(0, verbose_stream() << "Worker " << id << " canceling\n");
                m.limit().cancel();
            }
            void collect_statistics(::statistics& st) const {
                IF_VERBOSE(0, verbose_stream() << "Collecting statistics for worker " << id << "\n");
                ctx->collect_statistics(st);
            }
            reslimit& limit() {
                return m.limit();
            }
        };

        batch_manager m_batch_manager;
        ptr_vector<worker> m_workers;

    public:
        parallel(context& ctx) : 
            ctx(ctx),
            num_threads(std::min(
                (unsigned)std::thread::hardware_concurrency(),
                ctx.get_fparams().m_threads)),
            m_batch_manager(ctx.m, *this) {}

        lbool operator()(expr_ref_vector const& asms);

    };

}
