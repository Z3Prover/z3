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
#include <condition_variable>


namespace smt {

    struct cube_config {
        using literal = expr_ref;
        static bool literal_is_null(expr_ref const& l) { return l == nullptr; }
        static std::ostream& display_literal(std::ostream& out, expr_ref const& l) { return out << mk_bounded_pp(l, l.get_manager()); }
    };

    class parallel {
        context& ctx;

        struct shared_clause {
            unsigned source_worker_id;
            expr_ref clause;
        };

        struct bb_candidate {
            expr_ref lit;
            double age;
            unsigned hits;     // how many cubes reported it
            bb_candidate(ast_manager& m, expr* e, double s, unsigned h) : lit(e, m), age(s), hits(h) {}
        };

        using bb_candidates = vector<bb_candidate>;

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

            bb_candidates m_bb_candidates;
            unsigned m_max_global_bb_candidates = 100;
            unsigned m_bb_batch_size = 150;
            expr_ref_vector m_global_backbones;

            // Backbone job queue
            std::condition_variable m_bb_cv;
            bb_candidates m_bb_current_batch;
            unsigned m_bb_batch_id = 0;
            unsigned num_global_bb_threads = 0;
            unsigned_vector m_bb_last_batch_processed;
            unsigned m_bb_cancel_epoch = 0; // When a backbone worker finishes early, it increments m_bb_cancel_epoch and notifies all

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

            void cancel_backbones_worker() {
                IF_VERBOSE(1, verbose_stream() << "Canceling backbones workers\n");
                for (auto* w : p.m_global_backbones_workers)
                    w->cancel();
            }

            void cancel_background_threads() {
                cancel_workers();
                cancel_sls_worker();
                if (!p.m_global_backbones_workers.empty()) {
                    cancel_backbones_worker();
                    m_bb_cv.notify_all();
                }
            }

            // to avoid deadlock
            bool is_global_backbone_unlocked(ast_translation& l2g, expr* bb_cand) {
                expr_ref cand(l2g(bb_cand), l2g.to());
                return any_of(m_global_backbones, [&](expr *bb) { return bb == cand.get(); });
            }

            void backtrack_unlocked(ast_translation &l2g, expr_ref_vector const &core, node *n);
            void collect_clause_unlocked(ast_translation &l2g, unsigned source_worker_id, expr *clause);


        public:
            batch_manager(ast_manager& m, parallel& p) : m(m), p(p), m_search_tree(expr_ref(m)), m_global_backbones(m) { }

            void initialize(unsigned initial_max_thread_conflicts = 1000); // TODO: pass in from worker defaults

            void set_unsat(ast_translation& l2g, expr_ref_vector const& unsat_core);
            void set_sat(ast_translation& l2g, model& m);
            void set_exception(std::string const& msg);
            void set_exception(unsigned error_code);
            void collect_statistics(::statistics& st) const;

            void collect_backbone_candidates(ast_translation& l2g, bb_candidates& bb_candidates);
            bool collect_global_backbone(ast_translation& l2g, expr_ref const& backbone);
            bool wait_for_backbone_job(unsigned bb_thread_id, ast_translation& g2l, vector<parallel::bb_candidate>& out, reslimit& lim);
            bb_candidates return_global_bb_candidates(ast_translation& g2l);

            bool get_cube(ast_translation& g2l, unsigned id, expr_ref_vector& cube, node*& n);
            void backtrack(ast_translation& l2g, expr_ref_vector const& core, node* n);
            void try_split(ast_translation& l2g, unsigned id, node* n, expr* atom, unsigned effort);

            void collect_clause(ast_translation& l2g, unsigned source_worker_id, expr* clause);
            expr_ref_vector return_shared_clauses(ast_translation& g2l, unsigned& worker_limit, unsigned worker_id);

            lbool get_result() const;

            bool is_global_backbone(ast_translation& l2g, expr* bb_cand) {
                std::scoped_lock lock(mux);
                return is_global_backbone_unlocked(l2g, bb_cand);
            }

            void set_num_backbone_threads(unsigned n) {
                std::scoped_lock lock(mux);
                num_global_bb_threads = n;
                m_bb_last_batch_processed.reset();
                m_bb_last_batch_processed.resize(n);
            }

            void cancel_current_backbone_batch() {
                std::scoped_lock lock(mux);
                m_bb_cancel_epoch++;
                m_bb_cv.notify_all();
            }

            unsigned get_cancel_epoch() {
                std::scoped_lock lock(mux);
                return m_bb_cancel_epoch;
            }
        };

        class worker {
            struct config {
                unsigned m_threads_max_conflicts = 1000;
                bool m_share_units = true;
                bool m_share_conflicts = true;
                bool m_share_units_relevant_only = true;
                bool m_share_units_initial_only = true;
                bool m_share_theory_lemmas = false;
                unsigned m_share_theory_lemmas_max_lits = 8;
                double m_max_conflict_mul = 1.5;
                bool m_inprocessing = false;
                bool m_global_backbones = false;
                bool m_local_backbones = false;
                bool m_sls = false;
                unsigned m_inprocessing_delay = 1;
                unsigned m_max_cube_depth = 20;
                unsigned m_max_conflicts = UINT_MAX;
            };

            using node = search_tree::node<cube_config>;

            unsigned id; // unique identifier for the worker
            lbool mode; // l_undef - standard mode, l_true - sat mode, l_false - unsat mode
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
            unsigned m_num_shared_lemmas = 0;
            unsigned m_num_initial_atoms = 0;
            unsigned m_shared_clause_limit = 0; // remembers the index into shared_clause_trail marking the boundary between "old" and "new" clauses to share
            
            expr_ref get_split_atom();

            lbool check_cube(expr_ref_vector const& cube);
            void share_units();
            void share_theory_lemmas();

            void update_max_thread_conflicts() {
                m_config.m_threads_max_conflicts = (unsigned)(m_config.m_max_conflict_mul * m_config.m_threads_max_conflicts);
            } // allow for backoff scheme of conflicts within the thread for cube timeouts.

            void simplify();
            bb_candidates find_backbone_candidates(unsigned k = 10);
            void prepare_backbone_candidates(u_map<double>& original_activities);

        public:
            worker(unsigned id, parallel& p, expr_ref_vector const& _asms, lbool mode);
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

        class backbones_worker {
            struct stats {
                unsigned m_batches_total = 0;
                unsigned m_candidates_total = 0;
                unsigned m_singleton_backbones = 0;
                unsigned m_backbones_detected = 0;
                unsigned m_backbones_found = 0;
                unsigned m_fallback_singleton_checks = 0;
                unsigned m_fallback_reason_chunk_exhausted = 0;
                unsigned m_fallback_reason_undef = 0;
                unsigned m_core_refinement_rounds = 0;
                unsigned m_lits_removed_by_core = 0;
                unsigned m_num_chunk_increases = 0;
            };

            enum bb_mode {
                bb_negated,
                bb_positive
            };

            unsigned id; // unique identifier for the worker
            batch_manager& b;
            ast_manager m;
            expr_ref_vector asms;
            smt_params m_smt_params;
            scoped_ptr<context> ctx;
            ast_translation m_g2l, m_l2g;
            unsigned m_bb_chunk_size = 20;
            unsigned m_bb_conflicts_per_chunk = 1000;
            stats m_stats;
            bb_mode m_mode;
            unsigned num_global_bb_threads = 1; // used to toggle behavior when testing bb candidates 
            unsigned m_shared_clause_limit = 0; // remembers the index into shared_clause_trail marking the boundary between "old" and "new" clauses to share
            bool check_backbone(expr* bb_candidate);
        public:
            backbones_worker(unsigned id, parallel &p, expr_ref_vector const &_asms);
            void cancel();
            void collect_statistics(::statistics& st) const;
            void run();
            void collect_shared_clauses();
            reslimit &limit() { return m.limit(); }            
        };

        batch_manager m_batch_manager;
        scoped_ptr_vector<worker> m_workers;
        scoped_ptr<sls_worker> m_sls_worker;
        scoped_ptr_vector<backbones_worker> m_global_backbones_workers;

    public:
        parallel(context& ctx) : 
            ctx(ctx),
            m_batch_manager(ctx.m, *this) {}

        lbool operator()(expr_ref_vector const& asms);
    };

}
