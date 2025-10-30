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
// #include "util/util.h"
#include <thread>
#include <mutex>


namespace smt {

  inline bool operator==(const smt_params& a, const smt_params& b) {
      return a.m_nl_arith_branching == b.m_nl_arith_branching &&
            a.m_nl_arith_cross_nested == b.m_nl_arith_cross_nested &&
            a.m_nl_arith_delay == b.m_nl_arith_delay &&
            a.m_nl_arith_expensive_patching == b.m_nl_arith_expensive_patching &&
            a.m_nl_arith_gb == b.m_nl_arith_gb &&
            a.m_nl_arith_horner == b.m_nl_arith_horner &&
            a.m_nl_arith_horner_frequency == b.m_nl_arith_horner_frequency &&
            a.m_nl_arith_optimize_bounds == b.m_nl_arith_optimize_bounds &&
            a.m_nl_arith_propagate_linear_monomials == b.m_nl_arith_propagate_linear_monomials &&
            a.m_nl_arith_tangents == b.m_nl_arith_tangents;
  }

  inline bool operator!=(const smt_params& a, const smt_params& b) {
      return !(a == b);
  }

    struct cube_config {
        using literal = expr_ref;
        static bool literal_is_null(expr_ref const& l) { return l == nullptr; }
        static std::ostream& display_literal(std::ostream& out, expr_ref const& l) { return out << mk_bounded_pp(l, l.get_manager()); }
    };

    class parallel {
        context& ctx;
        unsigned num_threads;

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

        // life cycle of 
        // 1. proof prefix with cubes
        // 2. restart N separate contexts to check N new permutations of parameters.
        //    - one of the contexts uses the current configuration.
        // 3. pick winner configuration if any are better than current.
        // 4. update current configuration with the winner

        class param_generator {
            parallel& p;
            batch_manager& b;
            ast_manager m;
            scoped_ptr<context> ctx;
            ast_translation m_l2g;
            
            unsigned N = 4; // number of prefix permutations to test (including current)
            unsigned m_max_prefix_conflicts = 1000;
            
            scoped_ptr<context> m_prefix_solver;
            scoped_ptr_vector<context> m_param_probe_contexts;
            smt_params m_param_state;
            params_ref m_p;
            
            private:
                void init_param_state() {
                    m_param_state.m_nl_arith_branching = true;
                    m_param_state.m_nl_arith_cross_nested = true;
                    m_param_state.m_nl_arith_delay = 10;
                    m_param_state.m_nl_arith_expensive_patching = false;
                    m_param_state.m_nl_arith_gb = true;
                    m_param_state.m_nl_arith_horner = true;
                    m_param_state.m_nl_arith_horner_frequency = 4;
                    m_param_state.m_nl_arith_optimize_bounds = true;
                    m_param_state.m_nl_arith_propagate_linear_monomials = true;
                    m_param_state.m_nl_arith_tangents = true;

                    m_param_state.updt_params(m_p);
                    ctx->updt_params(m_p);
                };

                smt_params mutate_param_state() {
                    smt_params p = m_param_state;
                    random_gen m_rand;

                    auto flip_bool = [&](bool &x) {
                        if ((m_rand() % 2) == 0)
                            x = !x;
                    };

                    auto mutate_uint = [&](unsigned &x, unsigned lo, unsigned hi) {
                        if ((m_rand() % 2) == 0)
                            x = lo + (m_rand() % (hi - lo + 1));
                    };

                    flip_bool(p.m_nl_arith_branching);
                    flip_bool(p.m_nl_arith_cross_nested);
                    mutate_uint(p.m_nl_arith_delay, 5, 20);
                    flip_bool(p.m_nl_arith_expensive_patching);
                    flip_bool(p.m_nl_arith_gb);
                    flip_bool(p.m_nl_arith_horner);
                    mutate_uint(p.m_nl_arith_horner_frequency, 2, 6);
                    flip_bool(p.m_nl_arith_optimize_bounds);
                    flip_bool(p.m_nl_arith_propagate_linear_monomials);
                    flip_bool(p.m_nl_arith_tangents);

                    return p;
                }

            public:
                param_generator(parallel& p);
                lbool run_prefix_step();
                void protocol_iteration();
                unsigned replay_proof_prefixes(vector<smt_params> candidate_param_states, unsigned max_conflicts_epsilon);

                reslimit& limit() {
                    return m.limit();
                }
        };

        class worker {
            struct config {
                unsigned m_threads_max_conflicts = 1000;
                bool m_share_units = true;
                bool m_share_units_relevant_only = true;
                bool m_share_units_initial_only = true;
                double m_max_conflict_mul = 1.5;
                bool m_cube_initial_only = true;
                bool m_inprocessing = true;
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

        batch_manager m_batch_manager;
        scoped_ptr_vector<worker> m_workers;
        param_generator m_param_generator;

    public:
        parallel(context& ctx) : 
            ctx(ctx),
            num_threads(std::min(
                (unsigned)std::thread::hardware_concurrency(),
                ctx.get_fparams().m_threads)),
            m_batch_manager(ctx.m, *this),
            m_param_generator(*this) {}

        lbool operator()(expr_ref_vector const& asms);
    };

}
