/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_parallel.h

Abstract:

    Parallel SMT, portfolio loop specialized to SMT core.

Author:

    Ilana 2025

Revision History:

--*/
#pragma once

#include "smt/smt_context.h"
#include "smt/CubeTree.h"

#include <thread>
#include <map>
#include <queue>
#include <vector>

namespace smt {

    class parallel {
        context& ctx;
        unsigned num_threads;

        struct shared_clause {
            unsigned source_worker_id;
            expr_ref clause;
        };

        struct parameter_state {
            std::vector<std::pair<unsigned, double>> m_value_scores; // bounded number of values with scores.
            std::vector<std::pair<double, std::function<void(void)>>> m_weighted_moves; // possible moves weighted by how well they did
        };

        class batch_manager {        
            enum state {
                is_running,
                is_sat,
                is_unsat,
                is_exception_msg,
                is_exception_code
            };
            struct config {
                unsigned m_max_cube_depth = 20;
                bool m_frugal_cube_only = false;
                bool m_never_cube = false; 
                bool m_depth_splitting_only = false;
                bool m_iterative_deepening = false;
                bool m_beam_search = false;
                bool m_cubetree = false;
            };
            struct stats {
                unsigned m_max_cube_depth = 0;
                unsigned m_num_cubes = 0;
            };

            ast_manager& m;
            parallel& p;
            std::mutex mux;
            state m_state = state::is_running;
            config m_config;
            stats m_stats;
            expr_ref_vector m_split_atoms; // atoms to split on
            vector<expr_ref_vector> m_cubes;
            CubeTree m_cubes_tree;
            
            struct ScoredCube {
                double score;
                expr_ref_vector cube;
                
                ScoredCube(unsigned s, expr_ref_vector const& c) : score(s), cube(c) {}
            };

            // higher score = higher priority
            struct ScoredCubeCompare {
                bool operator()(ScoredCube const& a, ScoredCube const& b) const {
                    return a.score < b.score; 
                }
            };

            using CubePQ = std::priority_queue<
                ScoredCube, 
                std::vector<ScoredCube>, 
                ScoredCubeCompare
            >;

            CubePQ m_cubes_pq;

            std::map<unsigned, vector<expr_ref_vector>> m_cubes_depth_sets; // map<vec<cube>> contains sets of cubes, key is depth/size of cubes in the set
            unsigned m_max_batch_size = 10;
            unsigned m_exception_code = 0;
            std::string m_exception_msg;
            vector<shared_clause> shared_clause_trail; // store all shared clauses with worker IDs
            obj_hashtable<expr> shared_clause_set; // for duplicate filtering on per-thread clause expressions
            vector<parameter_state> m_parameters_state;

            double m_avg_cube_hardness = 0.0;
            unsigned m_solved_cube_count = 0;

            // called from batch manager to cancel other workers if we've reached a verdict
            void cancel_workers() {
                IF_VERBOSE(1, verbose_stream() << "Canceling workers\n");
                for (auto& w : p.m_workers) 
                    w->cancel();
            }

            void init_parameters_state();

        public:
            batch_manager(ast_manager& m, parallel& p) : m(m), p(p), m_split_atoms(m), m_cubes_tree(m) { }

            void initialize();

            void set_unsat(ast_translation& l2g, expr_ref_vector const& unsat_core);
            void set_sat(ast_translation& l2g, model& m);
            void set_exception(std::string const& msg);
            void set_exception(unsigned error_code);

            //
            // worker threads ask the batch manager for a cube to check.
            // they pass in a translation function from the global context to local context (ast-manager). It is called g2l.
            // The batch manager returns the next cube to
            //
            expr_ref_vector get_cube(ast_translation& g2l);  // FOR ALL NON-TREE VERSIONS

            std::pair<CubeNode*, expr_ref_vector> get_cube_from_tree(ast_translation& g2l, std::vector<CubeNode*>& frontier_roots, unsigned worker_id, CubeNode* prev_cube = nullptr);


            //
            // worker threads return unprocessed cubes to the batch manager together with split literal candidates.
            // the batch manager re-enqueues unprocessed cubes and optionally splits them using the split_atoms returned by this and workers.
            // 

            void return_cubes_tree(ast_translation& l2g, CubeNode* cube_node, expr_ref_vector const& cube, expr_ref_vector const& split_atoms, std::vector<CubeNode*>& frontier_roots);

            // FOR ALL NON-TREE VERSIONS
            void return_cubes(ast_translation& l2g, expr_ref_vector const& cube, expr_ref_vector const& split_atoms, const bool should_split=true, const double hardness=1.0);
            void report_assumption_used(ast_translation& l2g, expr* assumption);
            void collect_clause(ast_translation& l2g, unsigned source_worker_id, expr* e);
            expr_ref_vector return_shared_clauses(ast_translation& g2l, unsigned& worker_limit, unsigned worker_id);

            void remove_node_and_propagate(CubeNode* node) {
                std::scoped_lock lock(mux);
                SASSERT(m_config.m_cubetree);
                CubeNode* last_removed = m_cubes_tree.remove_node_and_propagate(node);
                if (last_removed) {
                    IF_VERBOSE(1, verbose_stream() << "Cube tree: removed node and propagated up to depth " << last_removed->cube.size() << "\n");
                } else {
                    IF_VERBOSE(1, verbose_stream() << "Cube tree: ERROR removing node with no propagation\n");
                }
            }

            double update_avg_cube_hardness(double hardness) {
                std::scoped_lock lock(mux);
                IF_VERBOSE(1, verbose_stream() << "Cube hardness: " << hardness << ", previous avg: " << m_avg_cube_hardness << ", solved cubes: " << m_solved_cube_count << "\n";);
                m_avg_cube_hardness = (m_avg_cube_hardness * m_solved_cube_count + hardness) / (m_solved_cube_count + 1);
                m_solved_cube_count++;
                return m_avg_cube_hardness;
            }

            void collect_statistics(::statistics& st) const;
            lbool get_result() const;
        };

        class worker {
            struct config {
                unsigned m_threads_max_conflicts = 1000;
                unsigned m_max_conflicts = 10000000;
                bool m_relevant_units_only = true;
                bool m_never_cube = false;
                bool m_share_conflicts = true;
                bool m_share_units = true;
                double m_max_conflict_mul = 1.5;
                bool m_share_units_initial_only = false;
                bool m_cube_initial_only = false;
                unsigned m_max_greedy_cubes = 1000;
                unsigned m_num_split_lits = 2;
                bool m_backbone_detection = false;
                bool m_iterative_deepening = false;
                bool m_beam_search = false;
                bool m_explicit_hardness = false;
                bool m_cubetree = false;
            };

            unsigned id; // unique identifier for the worker
            parallel& p;
            batch_manager& b;
            ast_manager m;
            expr_ref_vector asms;
            smt_params m_smt_params;
            config m_config;
            scoped_ptr<context> ctx;
            ast_translation m_g2l, m_l2g;
            CubeNode* m_curr_cube_node = nullptr;
            std::vector<CubeNode*> frontier_roots;

            unsigned m_num_shared_units = 0;
            unsigned m_num_initial_atoms = 0;
            unsigned m_shared_clause_limit = 0; // remembers the index into shared_clause_trail marking the boundary between "old" and "new" clauses to share
            
            
            void share_units(ast_translation& l2g);
            lbool check_cube(expr_ref_vector const& cube);
            void update_max_thread_conflicts() {
                m_config.m_threads_max_conflicts = (unsigned)(m_config.m_max_conflict_mul * m_config.m_threads_max_conflicts);
            } // allow for backoff scheme of conflicts within the thread for cube timeouts.

            expr_ref_vector find_backbone_candidates();
            expr_ref_vector get_backbones_from_candidates(expr_ref_vector const& candidates);
            
            double naive_hardness();
            double explicit_hardness(expr_ref_vector const& cube);
        public:
            worker(unsigned id, parallel& p, expr_ref_vector const& _asms);
            void run();
            expr_ref_vector get_split_atoms();
            void collect_shared_clauses(ast_translation& g2l);

            void cancel();
            void collect_statistics(::statistics& st) const;

            reslimit& limit() {
                return m.limit();
            }
        };

        obj_hashtable<expr> m_assumptions_used; // assumptions used in unsat cores, to be used in final core
        batch_manager m_batch_manager;
        scoped_ptr_vector<worker> m_workers;

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
