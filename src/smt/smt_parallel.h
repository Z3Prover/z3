/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_parallel.h

Abstract:

    Parallel SMT, portfolio loop specialized to SMT core.

Author:

    Ilana Shapiro - 2025

Revision History:

--*/
#pragma once

#include "smt/smt_context.h"
#include "util/search_tree.h"
#include "ast/sls/sls_smt_solver.h"
#include <thread>
#include <mutex>


namespace smt {

    struct cube_config {
        using literal = expr_ref;
        static bool literal_is_null(expr_ref const& l) { return l == nullptr; }
        static std::ostream& display_literal(std::ostream& out, expr_ref const& l) { return out << mk_bounded_pp(l, l.get_manager()); }
    };

    class parallel {
        context& ctx;
        unsigned num_threads;
        bool m_should_run_sls = false;

        struct shared_clause {
            unsigned source_worker_id;
            expr_ref clause;
        };

        class batch_manager {        

            enum state {
                is_running,
                is_sat,
                is_unsat,
                is_exception_msg,
                is_exception_code
            };

            struct stats {
                unsigned m_max_cube_depth = 0;
                unsigned m_num_cubes = 0;
            };


            ast_manager& m;
            parallel& p;
            std::mutex mux;
            state m_state = state::is_running;
            stats m_stats;
            using node = search_tree::node<cube_config>;
            search_tree::tree<cube_config> m_search_tree;
            
            unsigned m_exception_code = 0;
            std::string m_exception_msg;
            vector<shared_clause> shared_clause_trail; // store all shared clauses with worker IDs
            obj_hashtable<expr> shared_clause_set; // for duplicate filtering on per-thread clause expressions

            // called from batch manager to cancel other workers if we've reached a verdict
            void cancel_workers() {
                IF_VERBOSE(1, verbose_stream() << "Canceling workers\n");
                for (auto& w : p.m_workers) 
                    w->cancel();
            }

            void cancel_sls_worker() {
                if (!p.m_sls_worker)
                    return;
                IF_VERBOSE(1, verbose_stream() << "Canceling SLS worker\n");
                p.m_sls_worker->cancel();
            }

            void cancel_background_threads() {
                cancel_workers();
                cancel_sls_worker();  
            }

            void init_parameters_state();

        public:
            batch_manager(ast_manager& m, parallel& p) : m(m), p(p), m_search_tree(expr_ref(m)) { }

            void initialize();

            void set_unsat(ast_translation& l2g, expr_ref_vector const& unsat_core);
            void set_sat(ast_translation& l2g, model& m);
            void set_exception(std::string const& msg);
            void set_exception(unsigned error_code);
            void collect_statistics(::statistics& st) const;

            bool get_cube(ast_translation& g2l, unsigned id, expr_ref_vector& cube, node*& n);
            void backtrack(ast_translation& l2g, expr_ref_vector const& core, node* n);
            void split(ast_translation& l2g, unsigned id, node* n, expr* atom);

            void collect_clause(ast_translation& l2g, unsigned source_worker_id, expr* clause);
            expr_ref_vector return_shared_clauses(ast_translation& g2l, unsigned& worker_limit, unsigned worker_id);

            lbool get_result() const;
        };

        class worker {
            struct config {
                unsigned m_threads_max_conflicts = 1000;
                bool m_share_units = true;
                bool m_share_conflicts = true;
                bool m_share_units_relevant_only = true;
                bool m_share_units_initial_only = true;
                double m_max_conflict_mul = 1.5;
                bool m_inprocessing = false;
                bool m_sls = false;
                unsigned m_inprocessing_delay = 1;
                unsigned m_max_cube_depth = 20;
                unsigned m_max_conflicts = UINT_MAX;
            };

            using node = search_tree::node<cube_config>;

            unsigned id; // unique identifier for the worker
            parallel& p;
            batch_manager& b;
            ast_manager m;
            expr_ref_vector asms;
            smt_params m_smt_params;
            config m_config;
            random_gen m_rand;
            scoped_ptr<context> ctx;
            ast_translation m_g2l, m_l2g;

            unsigned m_num_shared_units = 0;
            unsigned m_num_initial_atoms = 0;
            unsigned m_shared_clause_limit = 0; // remembers the index into shared_clause_trail marking the boundary between "old" and "new" clauses to share
            
            expr_ref get_split_atom();

            lbool check_cube(expr_ref_vector const& cube);
            void share_units();

            void update_max_thread_conflicts() {
                m_config.m_threads_max_conflicts = (unsigned)(m_config.m_max_conflict_mul * m_config.m_threads_max_conflicts);
            } // allow for backoff scheme of conflicts within the thread for cube timeouts.

            void simplify();

        public:
            worker(unsigned id, parallel& p, expr_ref_vector const& _asms);
            void run();
            
            void collect_shared_clauses();

            void cancel();
            void collect_statistics(::statistics& st) const;

            reslimit& limit() {
                return m.limit();
            }

        };

        class sls_worker {
            parallel &p;
            batch_manager &b;
            ast_manager m;
            ast_translation m_g2l, m_l2g;
            scoped_ptr<sls::smt_solver> m_sls;
            params_ref m_params;

            public:
                sls_worker(parallel &p);
                void cancel();
                void run();
                void collect_statistics(::statistics& st) const;

                reslimit &limit() {
                    return m.limit();
                }
        };

        batch_manager m_batch_manager;
        scoped_ptr_vector<worker> m_workers;
        scoped_ptr<sls_worker> m_sls_worker;

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
