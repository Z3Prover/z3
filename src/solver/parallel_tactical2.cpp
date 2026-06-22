/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    parallel_tactical2.cpp

Abstract:

    Parallel tactical, portfolio loop specialized to the solver API.

Author:

    (based on smt_parallel.cpp by nbjorner / Ilana Shapiro, and
     parallel_tactical.cpp by nbjorner / Miguel Neves)

--*/

#include "util/scoped_ptr_vector.h"
#include "util/uint_set.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_util.h"
#include "ast/ast_translation.h"
#include "solver/solver.h"
#include "solver/parallel_tactical2.h"
#include "solver/parallel_params.hpp"
#include "util/search_tree.h"
#include "tactic/tactic.h"
#include "solver/solver2tactic.h"

#include <algorithm>
#include <cmath>
#include <cstring>
#include <mutex>
#include <utility>

/* ------------------------------------------------------------------ */
/* Single-threaded stub                                                 */
/* ------------------------------------------------------------------ */

class non_parallel_tactic2 : public tactic {
public:
    non_parallel_tactic2(solver*, params_ref const&) {}
    char const* name() const override { return "parallel_tactic2"; }
    void operator()(const goal_ref&, goal_ref_buffer&) override {
        throw default_exception("parallel_tactic2 is disabled in single-threaded mode");
    }
    tactic* translate(ast_manager&) override { return nullptr; }
    void cleanup() override {}
};

#ifdef SINGLE_THREAD

tactic* mk_parallel_tactic2(solver* s, params_ref const& p) {
    return alloc(non_parallel_tactic2, s, p);
}

#else

#include <atomic>
#include <thread>
#include <condition_variable>

#define LOG_WORKER(lvl, s) IF_VERBOSE(lvl, verbose_stream() << "Worker " << id << s)
#define LOG_BB_WORKER(lvl, s) IF_VERBOSE(lvl, verbose_stream() << "Backbones Worker " << id << s)

class bounded_pp_exprs {
    expr_ref_vector const &es;

public:
    bounded_pp_exprs(expr_ref_vector const &es) : es(es) {}

    std::ostream &display(std::ostream &out) const {
        for (auto e : es)
            out << mk_bounded_pp(e, es.get_manager()) << "\n";
        return out;
    }
};

inline std::ostream &operator<<(std::ostream &out, bounded_pp_exprs const &pp) {
    return pp.display(out);
}

/* ------------------------------------------------------------------ */
/* Search-tree literal configuration                                    */
/* ------------------------------------------------------------------ */

struct solver_cube_config {
    using literal = expr_ref;
    static bool literal_is_null(expr_ref const& l) { return l == nullptr; }
    static bool same_atom(expr_ref const& a, expr_ref const& b) {
        expr* atom_a = a.get();
        expr* atom_b = b.get();
        a.get_manager().is_not(atom_a, atom_a);
        b.get_manager().is_not(atom_b, atom_b);
        return atom_a == atom_b;
    }
    static std::ostream& display_literal(std::ostream& out, expr_ref const& l) {
        if (l) return out << mk_bounded_pp(l, l.get_manager());
        return out << "(null)";
    }
};

static bool is_cancellation_exception(char const* msg) {
    return msg && (strstr(msg, "canceled") != nullptr || strstr(msg, "cancelled") != nullptr);
}

/* ------------------------------------------------------------------ */
/* parallel_solver – the core portfolio engine                         */
/* ------------------------------------------------------------------ */

class parallel_solver {

    /* ---- forward declarations ---- */
    class worker;
    class core_minimizer_worker;
    class backbones_worker;

    /* ---- node lease (mirrors smt_parallel) ---- */
    struct node_lease {
        search_tree::node<solver_cube_config>* leased_node = nullptr;

        // Guards against multiple inc_cancel() calls for the same lease.
        // Set when cancel_lease() is signaled; cleared when a new lease is assigned.
        bool cancel_signaled  = false;
    };

    /* ---- shared clause entry ---- */
    struct shared_clause {
        unsigned source_worker_id;
        expr_ref clause;
    };

    struct bb_candidate {
        expr_ref lit;
        double age;
        unsigned hits;     // how many cubes reported it
        bb_candidate(ast_manager& m, expr* e, double s, unsigned h)
            : lit(e, m), age(s), hits(h) {}
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
            unsigned m_num_cubes      = 0;
            unsigned m_max_cube_depth = 0;
            unsigned m_backbones_found = 0;
            unsigned m_core_min_jobs_enqueued = 0;
            unsigned m_core_min_jobs_published = 0;
            unsigned m_core_min_jobs_skipped = 0;
            unsigned m_core_min_global_unsat = 0;
            unsigned m_bb_candidates_enqueued = 0;
            unsigned m_bb_batches_issued = 0;
        };

        struct core_min_job {
            search_tree::node<solver_cube_config>* source = nullptr;
            expr_ref_vector core;
            core_min_job(ast_manager& m, search_tree::node<solver_cube_config>* source)
                : source(source), core(m) {}
        };

        ast_manager&   m;
        parallel_solver& p;
        std::mutex     mux;
        state          m_state = state::is_running;
        stats          m_stats;

        search_tree::tree<solver_cube_config> m_search_tree;
        vector<node_lease> m_worker_leases;

        vector<shared_clause>    m_shared_clause_trail; // store all shared clauses with worker IDs
        obj_hashtable<expr>      m_shared_clause_set;   // for duplicate filtering on per-thread clause expressions

        obj_hashtable<expr>      m_global_backbones;

        bb_candidates            m_bb_candidates;
        unsigned                 m_max_global_bb_candidates = 100;
        unsigned                 m_bb_batch_size = 150;
        std::atomic<unsigned>    m_bb_candidate_epoch = 0;
        std::condition_variable  m_bb_cv;
        bb_candidates            m_bb_current_batch;
        unsigned                 m_bb_batch_id = 0;
        unsigned                 m_num_bb_threads = 0;
        unsigned_vector          m_bb_last_batch_processed;
        unsigned                 m_bb_cancel_epoch = 0; // When a backbone worker finishes early, it increments m_bb_cancel_epoch and notifies all

        // Core minimization job queue
        std::condition_variable   m_core_min_cv;
        scoped_ptr_vector<core_min_job> m_core_min_jobs;

        unsigned     m_exception_code = 0;
        std::string  m_exception_msg;
        model_ref    m_model;
        expr_ref_vector m_unsat_core;

        // called from batch manager to cancel other workers if we've reached a verdict
        void cancel_background_threads() {
            IF_VERBOSE(1, verbose_stream() << "Canceling workers\n");
            for (auto* w : p.m_workers)
                w->cancel();
            if (p.m_core_minimizer_worker) {
                p.m_core_minimizer_worker->cancel();
                m_core_min_cv.notify_all();
            }
            if (!p.m_global_backbones_workers.empty())
                IF_VERBOSE(1, verbose_stream() << "Canceling backbones workers\n");
            for (auto* w : p.m_global_backbones_workers)
                w->cancel();
            if (!p.m_global_backbones_workers.empty())
                m_bb_cv.notify_all();
        }

        void set_canceled_unlocked() {
            if (m_state != state::is_running)
                return;
            cancel_background_threads();
        }

        void release_worker_lease_unlocked(unsigned worker_id, node_lease& lease) {
            if (worker_id >= m_worker_leases.size()) {
                lease = {};
                return;
            }
            auto& stored_lease = m_worker_leases[worker_id];
            if (!stored_lease.leased_node || stored_lease.leased_node != lease.leased_node) {
                lease = {};
                return;
            }
            bool cancel_signaled = stored_lease.cancel_signaled;
            m_search_tree.dec_active_workers(stored_lease.leased_node);
            stored_lease = {};
            lease = {};
            if (cancel_signaled)
                p.m_workers[worker_id]->limit().dec_cancel();
        }

        bool attempt_release_canceled_lease_unlocked(unsigned worker_id, node_lease& lease) {
            if (m_state != state::is_running || !lease.leased_node || worker_id >= m_worker_leases.size())
                return false;

            auto& stored_lease = m_worker_leases[worker_id];
            if (stored_lease.leased_node != lease.leased_node)
                return false;

            if (!m_search_tree.is_lease_canceled(stored_lease.leased_node))
                return false;

            release_worker_lease_unlocked(worker_id, lease);
            return true;
        }

        void cancel_closed_leases_unlocked(unsigned source_worker_id) {
            unsigned n = std::min(m_worker_leases.size(), p.m_workers.size());
            for (unsigned id = 0; id < n; ++id) {
                if (id == source_worker_id) continue;
                auto const& lease = m_worker_leases[id];
                if (lease.leased_node && !lease.cancel_signaled &&
                    m_search_tree.is_lease_canceled(lease.leased_node)) {
                    m_worker_leases[id].cancel_signaled = true;
                    p.m_workers[id]->cancel_lease();
                }
            }
        }

        void collect_clause_unlocked(ast_translation& l2g, unsigned source_worker_id, expr* clause) {
            expr* g_clause = l2g(clause);
            if (!m_shared_clause_set.contains(g_clause)) {
                m_shared_clause_set.insert(g_clause);
                shared_clause sc{source_worker_id, expr_ref(g_clause, m)};
                m_shared_clause_trail.push_back(std::move(sc));
            }
        }

        // to avoid deadlock
        bool is_global_backbone_unlocked(ast_translation& l2g, expr* bb_cand) {
            expr_ref cand(l2g(bb_cand), m);
            return m_global_backbones.contains(cand.get());
        }

        bool is_global_backbone_or_negation_unlocked(ast_translation& l2g, expr* bb_cand) {
            expr_ref cand(l2g(bb_cand), m);
            expr_ref neg_cand(mk_not(m, cand), m);
            return m_global_backbones.contains(cand.get()) ||
                   m_global_backbones.contains(neg_cand.get());
        }

        void collect_matching_targets_unlocked(search_tree::node<solver_cube_config>* source,
                                               expr* lit,
                                               vector<solver_cube_config::literal> const& core,
                                               vector<node_lease>& targets) {
            targets.reset();
            if (!lit)
                return;

            auto is_ancestor_of = [&](search_tree::node<solver_cube_config>* ancestor,
                                      search_tree::node<solver_cube_config>* cur) {
                if (!ancestor)
                    return false;
                for (auto* p = cur; p; p = p->parent()) {
                    if (p == ancestor)
                        return true;
                }
                return false;
            };

            auto path_contains = [&](search_tree::node<solver_cube_config>* cur,
                                     solver_cube_config::literal const& lit0) {
                for (auto* p = cur; p; p = p->parent()) {
                    if (p->get_literal() == lit0)
                        return true;
                }
                return false;
            };

            auto path_contains_core = [&](search_tree::node<solver_cube_config>* cur) {
                return all_of(core, [&](solver_cube_config::literal const& c) {
                    return path_contains(cur, c);
                });
            };

            ptr_vector<search_tree::node<solver_cube_config>> matches;
            m_search_tree.find_nonclosed_nodes_with_literal(expr_ref(lit, m), matches);
            for (auto* t : matches) {
                if (!t || t == source)
                    continue;
                if (m_search_tree.is_lease_canceled(t))
                    continue;

                // When source is provided, keep only external matches. Nodes in the
                // same branch are already closed by backtracking on the source node.
                if (source && (is_ancestor_of(source, t) || is_ancestor_of(t, source)))
                    continue;

                // Reusing a conflict on another branch is sound only if that
                // the path from that node->root contains every literal in the core.
                // Matching on the closing literal alone is insufficient: F & a & l
                // may be UNSAT while F & c & l is SAT.
                if (!path_contains_core(t))
                    continue;

                // Keep only highest matching nodes: closing an ancestor also closes
                // all of its matching descendants.
                bool is_highest_ancestor = true;
                for (auto* p = t->parent(); p; p = p->parent()) {
                    if (any_of(targets, [&](node_lease const& target) { return target.leased_node == p; })) {
                        is_highest_ancestor = false;
                        break;
                    }
                }
                if (!is_highest_ancestor)
                    continue;

                targets.push_back({ t });
            }
        }

        // Given a newly closed node, source, and its core, find the lowest ancestor of source that
        // contains a core literal, and return it as the source for the core minimization job
        search_tree::node<solver_cube_config>* find_core_source_unlocked(
            ast_translation& l2g, search_tree::node<solver_cube_config>* source, expr_ref_vector const& core) {
            if (!source)
                return nullptr;

            vector<solver_cube_config::literal> g_core;
            for (expr* c : core)
                g_core.push_back(expr_ref(l2g(c), m));

            for (auto* cur = source; cur; cur = cur->parent()) {
                if (solver_cube_config::literal_is_null(cur->get_literal()))
                    continue;
                if (any_of(g_core, [&](solver_cube_config::literal const& lit) { return lit == cur->get_literal(); }))
                    return cur;
            }
            return nullptr;
        }

        unsigned select_best_core_min_job_unlocked() const {
            SASSERT(!m_core_min_jobs.empty());
            unsigned best_idx = 0;
            auto* best_source = m_core_min_jobs[0]->source;
            unsigned best_depth = best_source ? best_source->depth() : 0;
            unsigned best_core_size = m_core_min_jobs[0]->core.size();

            for (unsigned i = 1; i < m_core_min_jobs.size(); ++i) {
                auto* job = m_core_min_jobs[i];
                auto* job_source = job->source;
                unsigned job_depth = job_source ? job_source->depth() : 0;
                unsigned job_core_size = job->core.size();

                // rank first by core source node depth (deepest -> shallowest), then by core size (largest -> smallest)
                if (job_depth > best_depth ||
                    (job_depth == best_depth && job_core_size > best_core_size)) {
                    best_idx = i;
                    best_depth = job_depth;
                    best_core_size = job_core_size;
                }
            }
            return best_idx;
        }

        void backtrack_unlocked(ast_translation& l2g, unsigned worker_id,
                                expr_ref_vector const& core,
                                node_lease* lease = nullptr,
                                vector<node_lease> const* targets = nullptr) {
            if (m_state != state::is_running)
                return;

            vector<solver_cube_config::literal> g_core;
            for (expr* c : core)
                g_core.push_back(expr_ref(l2g(c), m));

            SASSERT(lease != nullptr || targets != nullptr);
            bool did_backtrack = false;

            if (lease) {
                if (!m_search_tree.is_lease_canceled(lease->leased_node)) {
                    // we close/backtrack regardless of whether this lease is stale or not, as long as the lease isn't canceled
                    // i.e. worker 1 splits this node, but then worker 2 determines UNSAT --> worker 2 is stale but we still close this node and backtrack
                    did_backtrack = true;
                    IF_VERBOSE(1, verbose_stream() << "Batch manager backtracking.\n");
                    auto* leased_node = lease->leased_node;
                    release_worker_lease_unlocked(worker_id, *lease);
                    m_search_tree.backtrack(leased_node, g_core);
                }
                else { 
                    // the lease was canceled by another worker. don't backtrack on this node with the new, arbitrary core we just found with this thread
                    // however, we do proceed to external targets, since the new code may have exposed new external targets we can close/backtrack
                    attempt_release_canceled_lease_unlocked(worker_id, *lease);
                }
            }
            if (targets) {
                for (auto const& target : *targets) {
                    if (m_search_tree.is_lease_canceled(target.leased_node))
                        continue;
                    did_backtrack = true;
                    m_search_tree.backtrack(target.leased_node, g_core);
                }
            }
            if (!did_backtrack)
                return;

            // terminate on-demand the workers that are currently exploring the now-closed nodes
            cancel_closed_leases_unlocked(worker_id);

            IF_VERBOSE(2,
                for (expr* e : core)
                    verbose_stream() << mk_bounded_pp(e, core.get_manager()) << "\n";
                m_search_tree.display(verbose_stream() << "\n");
            );

            if (m_search_tree.is_closed()) {
                IF_VERBOSE(1, verbose_stream() << "Search tree closed, setting UNSAT\n");
                m_state = state::is_unsat;
                SASSERT(m_unsat_core.empty());
                for (auto& e : m_search_tree.get_core_from_root())
                    m_unsat_core.push_back(e.get());
                cancel_background_threads();
            }
        }

    public:

        batch_manager(ast_manager& m, parallel_solver& p)
            : m(m), p(p),
              m_search_tree(expr_ref(m)),
              m_unsat_core(m) {}

        void initialize(unsigned num_bb_threads, unsigned initial_max_thread_conflicts = 1000) {
            m_state = state::is_running;
            m_search_tree.reset();
            m_search_tree.set_effort_unit(initial_max_thread_conflicts);
            m_worker_leases.reset();
            m_worker_leases.resize(p.m_workers.size());
            m_shared_clause_trail.reset();
            m_shared_clause_set.reset();
            m_global_backbones.reset();
            m_bb_candidates.reset();
            m_bb_current_batch.reset();
            m_bb_batch_id = 0;
            m_num_bb_threads = num_bb_threads;
            m_bb_last_batch_processed.reset();
            m_bb_last_batch_processed.resize(num_bb_threads);
            m_bb_cancel_epoch = 0;
            m_bb_candidate_epoch.store(0, std::memory_order_release);
            m_core_min_jobs.reset();
            m_model = nullptr;
            m_unsat_core.reset();
        }

        void set_sat(ast_translation& l2g, model& mdl) {
            std::scoped_lock lock(mux);
            IF_VERBOSE(1, verbose_stream() << "Batch manager setting SAT.\n");
            if (m_state != state::is_running) return;
            m_state = state::is_sat;
            m_model = mdl.translate(l2g);
            cancel_background_threads();
        }

        void set_canceled() {
            std::scoped_lock lock(mux);
            set_canceled_unlocked();
        }
        
        void set_unsat(ast_translation& l2g,
                       expr_ref_vector const& core) {
            std::scoped_lock lock(mux);
            IF_VERBOSE(1, verbose_stream() << "Batch manager setting UNSAT.\n");
            if (m_state != state::is_running) return;
            m_state = state::is_unsat;
            SASSERT(m_unsat_core.empty());
            for (expr* c : core)
                m_unsat_core.push_back(l2g(c));
            cancel_background_threads();
        }

        void set_exception(std::string const& msg) {
            std::scoped_lock lock(mux);
            IF_VERBOSE(1, verbose_stream() << "Batch manager setting exception msg: " << msg << ".\n");
            if (m_state != state::is_running) return;
            m_state = state::is_exception_msg;
            m_exception_msg = msg;
            cancel_background_threads();
        }

        void set_exception(unsigned error_code) {
            std::scoped_lock lock(mux);
            IF_VERBOSE(1, verbose_stream() << "Batch manager setting exception code: " << error_code << ".\n");
            if (m_state != state::is_running) return;
            m_state = state::is_exception_code;
            m_exception_code = error_code;
            cancel_background_threads();
        }

        bool get_cube(ast_translation& g2l, unsigned id,
                      expr_ref_vector& cube, bool is_first_run,
                      node_lease& lease) {
            std::scoped_lock lock(mux);
            cube.reset();
            if (m_search_tree.is_closed()) return false;
            if (m_state != state::is_running) return false;

            auto* t = is_first_run
                ? m_search_tree.activate_root()
                : m_search_tree.activate_best_node();
            if (!t) return false;

            lease.leased_node  = t;
            if (id >= m_worker_leases.size())
                m_worker_leases.resize(id + 1);
            m_worker_leases[id] = lease;

            for (auto* cur = t; cur; cur = cur->parent()) {
                if (solver_cube_config::literal_is_null(cur->get_literal()))
                    break;
                cube.push_back(expr_ref(g2l(cur->get_literal().get()), g2l.to()));
            }
            return true;
        }

        void backtrack(ast_translation& l2g, unsigned worker_id,
                       expr_ref_vector const& core,
                       node_lease& lease) {
            std::scoped_lock lock(mux);
            if (m_state != state::is_running) return;
            vector<solver_cube_config::literal> g_core;
            for (expr* c : core)
                g_core.push_back(expr_ref(l2g(c), m));

            vector<node_lease> targets;
            expr* lit = lease.leased_node ? lease.leased_node->get_literal().get() : nullptr;
            collect_matching_targets_unlocked(lease.leased_node, lit, g_core, targets);
            backtrack_unlocked(l2g, worker_id, core, &lease, targets.empty() ? nullptr : &targets);
        }

        void enqueue_core_minimization(ast_translation& l2g,
                                       search_tree::node<solver_cube_config>* source,
                                       expr_ref_vector const& core) {
            std::scoped_lock lock(mux);
            if (m_state != state::is_running || !p.m_core_minimizer_worker || !source || core.empty())
                return;
            if (core.size() <= 1) {
                ++m_stats.m_core_min_jobs_skipped;
                return;
            }

            source = find_core_source_unlocked(l2g, source, core);
            if (!source) {
                ++m_stats.m_core_min_jobs_skipped;
                return;
            }

            scoped_ptr<core_min_job> job = alloc(core_min_job, m, source);
            for (expr* c : core)
                job->core.push_back(l2g(c));
            m_core_min_jobs.push_back(job.detach());
            ++m_stats.m_core_min_jobs_enqueued;
            m_core_min_cv.notify_one();
        }

        bool wait_for_core_min_job(ast_translation& g2l,
                                   search_tree::node<solver_cube_config>*& source,
                                   expr_ref_vector& core,
                                   reslimit& lim) {
            std::unique_lock lock(mux);
            m_core_min_cv.wait(lock, [&]() {
                return lim.is_canceled() || m_state != state::is_running || !m_core_min_jobs.empty();
            });

            if (lim.is_canceled() || m_state != state::is_running)
                return false;

            unsigned best_idx = select_best_core_min_job_unlocked();
            m_core_min_jobs.swap(best_idx, m_core_min_jobs.size() - 1);
            scoped_ptr<core_min_job> job = m_core_min_jobs.detach_back();
            m_core_min_jobs.pop_back();
            SASSERT(job);
            source = job->source;
            core.reset();
            for (expr* c : job->core)
                core.push_back(g2l(c));
            return source != nullptr;
        }

        void publish_minimized_core(ast_translation& l2g,
                                    expr_ref_vector const& asms,
                                    search_tree::node<solver_cube_config>* source,
                                    unsigned original_core_size,
                                    expr_ref_vector const& minimized_core) {
            std::scoped_lock lock(mux);
            if (m_state != state::is_running || !source || minimized_core.size() >= original_core_size) {
                ++m_stats.m_core_min_jobs_skipped;
                return;
            }

            vector<solver_cube_config::literal> g_core;
            for (expr* c : minimized_core)
                g_core.push_back(expr_ref(l2g(c), m));

            // don't publish a minimized core if the node already has an equal-or-smaller core by the time the minimizer thread finishes
            // (e.g. from another thread or from backtracking resolution propagation)
            if (source->get_core().size() <= g_core.size()) {
                ++m_stats.m_core_min_jobs_skipped;
                return;
            }

            if (all_of(g_core, [&](solver_cube_config::literal const& lit) { return asms.contains(lit.get()); })) {
                IF_VERBOSE(1, verbose_stream() << "Minimized core removed all path literals, setting UNSAT\n");
                m_state = state::is_unsat;
                SASSERT(m_unsat_core.empty());
                for (expr* e : minimized_core)
                    m_unsat_core.push_back(l2g(e));
                ++m_stats.m_core_min_jobs_published;
                ++m_stats.m_core_min_global_unsat;
                cancel_background_threads();
                return;
            }

            // do not backtrack through the batch manager since this only handles non-closed leases
            // and the batch manager also tries to search for external matching targets in the tree
            // which is a problem since we must backtrack only on the source node or the core is invalid
            m_search_tree.backtrack(source, g_core);

            vector<node_lease> targets;
            if (!g_core.empty()) {
                collect_matching_targets_unlocked(source, g_core[0].get(), g_core, targets);
                for (auto const& target : targets) {
                    if (!m_search_tree.is_lease_canceled(target.leased_node))
                        m_search_tree.backtrack(target.leased_node, g_core);
                }
            }

            ++m_stats.m_core_min_jobs_published;
            cancel_closed_leases_unlocked(UINT_MAX);

            IF_VERBOSE(1, verbose_stream() << "Batch manager publishing minimized core "
                                           << original_core_size << " -> " << minimized_core.size() << "\n");
            IF_VERBOSE(2,
                for (expr* e : minimized_core)
                    verbose_stream() << mk_bounded_pp(e, minimized_core.get_manager()) << "\n";
                m_search_tree.display(verbose_stream() << "\n");
            );
            if (m_search_tree.is_closed()) {
                IF_VERBOSE(1, verbose_stream() << "Search tree closed by minimized core, setting UNSAT\n");
                m_state = state::is_unsat;
                SASSERT(m_unsat_core.empty());
                for (auto& e : m_search_tree.get_core_from_root())
                    m_unsat_core.push_back(e.get());
                cancel_background_threads();
            }
        }

        bool path_contains_atom(ast_translation& l2g, node_lease const& lease, expr* atom) {
            std::scoped_lock lock(mux);
            if (!lease.leased_node)
                return false;
            if (m_state != state::is_running)
                return false;
            if (m_search_tree.is_lease_canceled(lease.leased_node))
                return false;

            expr_ref _atom(l2g(atom), m);
            return lease.leased_node->path_contains_atom(_atom);
        }

        void try_split(ast_translation& l2g, unsigned worker_id,
                       node_lease& lease, expr* atom, unsigned effort) {
            std::scoped_lock lock(mux);
            if (m_state != state::is_running) return;
            if (m_search_tree.is_lease_canceled(lease.leased_node)) {
                attempt_release_canceled_lease_unlocked(worker_id, lease);
                return;
            }

            expr_ref lit(m), nlit(m);
            auto* leased_node = lease.leased_node;
            lit  = l2g(atom);
            nlit = mk_not(m, lit);
            VERIFY(!leased_node->path_contains_atom(lit));
            VERIFY(!leased_node->path_contains_atom(nlit));

            bool did_split = m_search_tree.try_split(leased_node, lit, nlit, effort);

            release_worker_lease_unlocked(worker_id, lease);

            if (did_split) {
                ++m_stats.m_num_cubes;
                m_stats.m_max_cube_depth = std::max(
                    m_stats.m_max_cube_depth,
                    leased_node->depth() + 1);
                IF_VERBOSE(1, verbose_stream() << "Batch manager splitting on literal: " << mk_bounded_pp(lit, m, 3) << "\n");
            }
        }

        bool attempt_release_canceled_lease(unsigned worker_id, node_lease& lease) {
            std::scoped_lock lock(mux);
            return attempt_release_canceled_lease_unlocked(worker_id, lease);
        }

        bool checkpoint_worker(unsigned worker_id, node_lease& lease, bool& lease_canceled) {
            std::scoped_lock lock(mux);
            lease_canceled = false;
            SASSERT(worker_id < p.m_workers.size());

            if (attempt_release_canceled_lease_unlocked(worker_id, lease)) {
                lease_canceled = true;
                return true;
            }

            if (p.m_workers[worker_id]->limit().inc())
                return true;

            if (attempt_release_canceled_lease_unlocked(worker_id, lease)) {
                lease_canceled = true;
                return true;
            }

            set_canceled_unlocked();
            return false;
        }

        void collect_clause(ast_translation& l2g,
                            unsigned source_worker_id,
                            expr* clause) {
            std::scoped_lock lock(mux);
            collect_clause_unlocked(l2g, source_worker_id, clause);
        }

        expr_ref_vector return_shared_clauses(ast_translation& g2l, unsigned& worker_limit, unsigned worker_id) {
            std::scoped_lock lock(mux);
            expr_ref_vector result(g2l.to());
            for (unsigned i = worker_limit; i < m_shared_clause_trail.size(); ++i) {
                if (m_shared_clause_trail[i].source_worker_id != worker_id)
                    result.push_back(g2l(m_shared_clause_trail[i].clause.get()));
            }
            worker_limit = m_shared_clause_trail.size();  // update the worker limit to the end of the current trail
            return result;
        }

        bool collect_global_backbone(ast_translation& l2g, expr_ref const& backbone, unsigned source_worker_id = UINT_MAX) {
            std::scoped_lock lock(mux);
            IF_VERBOSE(1, verbose_stream() << "collect-global-backbone\n");
            if (is_global_backbone_unlocked(l2g, backbone.get()))
                return false;
            expr_ref g_bb(l2g(backbone.get()), m);
            m_global_backbones.insert(g_bb.get());
            ++m_stats.m_backbones_found;
            IF_VERBOSE(1, verbose_stream() << " Found and sharing new global backbone: " << mk_bounded_pp(g_bb, m, 3) << "\n");
            collect_clause_unlocked(l2g, source_worker_id, backbone.get());

            expr_ref neg_g_bb(mk_not(m, g_bb), m);
            vector<solver_cube_config::literal> g_core;
            g_core.push_back(neg_g_bb);
            vector<node_lease> targets;
            collect_matching_targets_unlocked(nullptr, neg_g_bb, g_core, targets);
            
            if (!targets.empty()) {
                IF_VERBOSE(1, verbose_stream() << " Closing negation of the new global backbone: "
                                               << mk_bounded_pp(g_bb, m, 3) << "\n");
                expr_ref_vector l_core(l2g.from());
                l_core.push_back(mk_not(backbone));
                backtrack_unlocked(l2g, UINT_MAX, l_core, nullptr, &targets);
            }
            
            return true;
        }

        bool is_global_backbone_or_negation(ast_translation& l2g, expr* bb_cand) {
            std::scoped_lock lock(mux);
            return is_global_backbone_or_negation_unlocked(l2g, bb_cand);
        }

        bool has_new_backbone_candidates(unsigned epoch) {
            return m_bb_candidate_epoch.load(std::memory_order_acquire) != epoch;
        }

        unsigned get_bb_candidate_epoch() const {
            return m_bb_candidate_epoch.load(std::memory_order_acquire);
        }

        void cancel_current_backbone_batch() {
            std::scoped_lock lock(mux);
            ++m_bb_cancel_epoch;
            m_bb_cv.notify_all();
        }

        unsigned get_cancel_epoch() {
            std::scoped_lock lock(mux);
            return m_bb_cancel_epoch;
        }

        expr_ref_vector get_global_backbones_snapshot(ast_translation& g2l) {
            std::scoped_lock lock(mux);
            expr_ref_vector snapshot(g2l.to());
            for (expr* gb : m_global_backbones)
                snapshot.push_back(g2l(gb));
            return snapshot;
        }

        void collect_backbone_candidates(ast_translation& l2g,
                                         bb_candidates& bb_candidates) {
            std::scoped_lock lock(mux);
            bool changed = false;

            auto find_existing_candidate_idx = [&](expr* e) -> int {
                for (unsigned i = 0; i < m_bb_candidates.size(); ++i) {
                    if (m_bb_candidates[i].lit.get() == e)
                        return i;
                }
                return -1;
            };

            auto rank_of = [&](bb_candidate const& c) {
                return c.age * std::log2(2.0 + c.hits);
            };

            for (auto const& c : bb_candidates) {
                expr_ref g_lit(l2g(c.lit.get()), m);
                if (is_global_backbone_or_negation_unlocked(l2g, c.lit.get()))
                    continue;

                double age = c.age;
                int idx = find_existing_candidate_idx(g_lit.get());
                if (idx >= 0) {
                    auto& existing = m_bb_candidates[idx];
                    existing.age = (existing.age * existing.hits + age) / (existing.hits + 1);
                    existing.hits++;
                    continue;
                }

                if (m_bb_candidates.size() < m_max_global_bb_candidates) {
                    m_bb_candidates.push_back(bb_candidate(m, g_lit.get(), age, 1));
                    changed = true;
                    continue;
                }

                bb_candidate incoming(m, g_lit.get(), age, 1);
                auto worst_it = std::min_element(
                    m_bb_candidates.begin(),
                    m_bb_candidates.end(),
                    [&](bb_candidate const& a, bb_candidate const& b) {
                        return rank_of(a) < rank_of(b);
                    });
                if (worst_it != m_bb_candidates.end() && rank_of(incoming) > rank_of(*worst_it)) {
                    *worst_it = incoming;
                    changed = true;
                }
            }

            if (changed && !m_bb_candidates.empty()) {
                m_bb_candidate_epoch.fetch_add(1, std::memory_order_release);
                std::stable_sort(
                    m_bb_candidates.begin(),
                    m_bb_candidates.end(),
                    [&](bb_candidate const& a, bb_candidate const& b) {
                        return rank_of(a) < rank_of(b);
                    });
                m_bb_cv.notify_all();
            }
        }

        bool wait_for_backbone_job(unsigned bb_thread_id, ast_translation& g2l,
                                   bb_candidates& out, reslimit& lim) {
            out.reset();
            std::unique_lock lock(mux);
            m_bb_cv.wait(lock, [&]() {
                return lim.is_canceled() ||
                       m_state != state::is_running ||
                       m_bb_last_batch_processed[bb_thread_id] < m_bb_batch_id ||
                       !m_bb_candidates.empty();
            });

            if (lim.is_canceled() || m_state != state::is_running)
                return false;

            if (m_bb_last_batch_processed[bb_thread_id] == m_bb_batch_id) {
                unsigned n = std::min<unsigned>(m_bb_batch_size, m_bb_candidates.size());
                m_bb_current_batch.reset();
                for (unsigned i = 0; i < n; ++i) {
                    m_bb_current_batch.push_back(m_bb_candidates.back());
                    m_bb_candidates.pop_back();
                }
                ++m_bb_batch_id;
                m_bb_cv.notify_all();
            }

            for (auto const& gc : m_bb_current_batch) {
                expr_ref l_lit(g2l(gc.lit.get()), g2l.to());
                out.push_back(bb_candidate(g2l.to(), l_lit, gc.age, gc.hits));
            }
            m_bb_last_batch_processed[bb_thread_id] = m_bb_batch_id;
            return true;
        }

        lbool get_result() const {
            if (m.limit().is_canceled())
                return l_undef;  // the main context was cancelled, so we return undef.
            switch (m_state) {
            case state::is_running:  // batch manager is still running, but all threads have processed their cubes, which
                                     // means all cubes were unsat
                throw default_exception("par2: inconsistent end state");
            case state::is_sat:             return l_true;
            case state::is_unsat:           return l_false;
            case state::is_exception_msg:
                throw default_exception(m_exception_msg.c_str());
            case state::is_exception_code:
                throw z3_error(m_exception_code);
            default:
                UNREACHABLE();
                return l_undef;
            }
        }

        model_ref& get_model() { return m_model; }

        expr_ref_vector const& get_unsat_core() const { return m_unsat_core; }

        void collect_statistics(statistics& st) const {
            st.update("parallel-num-cubes", m_stats.m_num_cubes);
            st.update("parallel-max-cube-size", m_stats.m_max_cube_depth);
            st.update("parallel-backbones-found", m_stats.m_backbones_found);
            st.update("parallel-core-min-jobs-enqueued", m_stats.m_core_min_jobs_enqueued);
            st.update("parallel-core-min-jobs-published", m_stats.m_core_min_jobs_published);
            st.update("parallel-core-min-jobs-skipped", m_stats.m_core_min_jobs_skipped);
            st.update("parallel-core-min-global-unsat", m_stats.m_core_min_global_unsat);
        }
    };

    /* ================================================================
     * worker
     * Each worker owns a translated copy of the original solver plus
     * its own ast_manager.  Workers communicate only through the
     * batch_manager (mutex-protected).
     * ================================================================ */
    class worker {
            struct config {
                unsigned m_threads_max_conflicts = 1000;
                double   m_max_conflict_mul      = 1.5;
                unsigned m_max_conflicts         = UINT_MAX;
                bool     m_share_units           = true;
                bool     m_share_conflicts       = true;
                bool     m_share_units_relevant_only = true;
                bool     m_share_units_initial_only = true;
                bool     m_core_minimize         = false;
                bool     m_global_backbones      = false;
                bool     m_ablate_backtracking   = false;
                unsigned m_max_cube_depth        = 20;
        };

        unsigned         id;
        batch_manager&   b;
        ast_manager      m;                 /* worker-local manager */
        ref<solver>      s;                 /* translated solver copy */
        expr_ref_vector  asms;              /* translated assumptions */
        ast_translation  m_g2l, m_l2g;     /* global↔local translations */
        config           m_config;
        uint_set         m_known_units;     /* bool vars already shared by this worker */
        unsigned         m_shared_clause_limit = 0;
        unsigned         m_shared_units_prefix = 0;
        unsigned         m_num_initial_atoms = 0;

        void update_max_thread_conflicts() {
            m_config.m_threads_max_conflicts = static_cast<unsigned>(
                m_config.m_max_conflict_mul * m_config.m_threads_max_conflicts);
        }

        lbool check_cube(expr_ref_vector const& cube) {
            s->set_max_conflicts(std::min(m_config.m_threads_max_conflicts, m_config.m_max_conflicts));

            expr_ref_vector combined(m);
            combined.append(asms);
            combined.append(cube);

            IF_VERBOSE(1, verbose_stream() << " Checking cube\n"
                                           << bounded_pp_exprs(cube)
                                           << "with max_conflicts: "
                                           << std::min(m_config.m_threads_max_conflicts, m_config.m_max_conflicts)
                                           << "\n";);
            lbool r = l_undef;
            try {
                r = s->check_sat(combined);
            }
            catch (z3_error& err) {
                if (!m.limit().is_canceled())
                    b.set_exception(err.error_code());
            }
            catch (z3_exception& ex) {
                if (!m.limit().is_canceled() && !is_cancellation_exception(ex.what()))
                    b.set_exception(ex.what());
            } 
            catch (...) {
                if (!m.limit().is_canceled())
                    b.set_exception("unknown exception");
            }
            LOG_WORKER(1, " DONE checking cube " << r << "\n";);
            return r;
        }

        void collect_shared_clauses() {
            expr_ref_vector nc = b.return_shared_clauses(m_g2l, m_shared_clause_limit, id);
            for (expr* e : nc) {
                LOG_WORKER(4, " asserting shared clause: " << mk_bounded_pp(e, m, 3) << "\n");
                s->assert_expr(e);
            }
        }

        void share_units() {
            if (!m_config.m_share_units) 
                return;
            expr_ref_vector trail = s->get_assigned_literals();
            unsigned sz = trail.size();
            unsigned prefix_sz = std::min(m_shared_units_prefix, sz);
            bool at_prefix = true;
            
            for (unsigned i = m_shared_units_prefix; i < sz; ++i) {
                expr* e = trail.get(i);
                if (s->get_assign_level(e) > 0) {
                    at_prefix = false;
                    continue;
                }

                if (at_prefix)
                    ++prefix_sz;

                expr* atom = e;
                m.is_not(e, atom);

                if (m.is_and(atom) || m.is_or(atom) || m.is_ite(atom) || m.is_iff(atom))
                    continue;

                unsigned v = s->get_bool_var(atom);
                if (v == UINT_MAX)
                    continue;
                if (m_known_units.contains(v)) 
                    continue;
                m_known_units.insert(v);

                if (m_config.m_share_units_relevant_only && !s->is_relevant(atom))
                    continue;
                if (m_config.m_share_units_initial_only && v >= m_num_initial_atoms)
                    continue;

                expr_ref lit(e, m);
                b.collect_global_backbone(m_l2g, lit, id);
            }
            m_shared_units_prefix = prefix_sz;
        }

        expr_ref get_split_atom(node_lease const& lease, expr_ref_vector const& cube) {
            expr_ref result(m);
            if (cube.size() >= m_config.m_max_cube_depth)
                return result;

            obj_hashtable<expr> invalid_split_atoms_set;
            expr_ref_vector invalid_split_atoms(m);
            auto mark_invalid_split_atom = [&](expr* lit) {
                expr* atom = lit;
                m.is_not(lit, atom);
                if (!invalid_split_atoms_set.contains(atom)) {
                    invalid_split_atoms_set.insert(atom);
                    invalid_split_atoms.push_back(atom);
                }
            };
            for (expr* lit : cube) { // don't split on atoms already in the cube
                mark_invalid_split_atom(lit);
            }
            if (m_config.m_global_backbones) { // don't split on global backbones or their negations
                expr_ref_vector global_backbones = b.get_global_backbones_snapshot(m_g2l);
                for (expr* lit : global_backbones) {
                    mark_invalid_split_atom(lit);
                }
            }

            try {
                return s->cube_vsids(invalid_split_atoms);
            }
            catch (...) {
                if (!m.limit().is_canceled())
                    b.set_exception("unknown exception");
                return result;
            }
            return result;
        }

        bb_candidates find_backbone_candidates(expr_ref_vector const& cube, unsigned k = 10) {
            bb_candidates result;
            vector<solver::scored_literal> cands;
            try {
                s->get_backbone_candidates(cands, s->get_num_bool_vars());
            } catch (z3_error& err) {
                if (!m.limit().is_canceled())
                    b.set_exception(err.error_code());
                return result;
            } catch (z3_exception &ex) {
                if (!m.limit().is_canceled() && !is_cancellation_exception(ex.what()))
                    b.set_exception(ex.what());
                return result;
            } catch (...) {
                if (!m.limit().is_canceled())
                    b.set_exception("unknown exception");
                return result;
            }
            for (auto const& cand : cands) {
                expr* lit = cand.lit.get();
                if (m_config.m_global_backbones &&
                    b.is_global_backbone_or_negation(m_l2g, lit))
                    continue;
                result.push_back(bb_candidate(m, lit, cand.score, 1));
                if (result.size() >= k)
                    break;
            }
            return result;
        }

    public:

        worker(unsigned id, parallel_solver& p, solver& src, params_ref const& params, expr_ref_vector const& src_asms)
            : id(id), b(p.m_batch_manager), asms(m), m_g2l(src.get_manager(), m), m_l2g(m, src.get_manager()) {
            parallel_params pp(params);
            m_config.m_core_minimize = pp.core_minimize();
            m_config.m_ablate_backtracking = pp.ablate_backtracking();
            m_config.m_global_backbones = pp.num_bb_threads() > 0;
            if (m_config.m_ablate_backtracking)
                m_config.m_core_minimize = false;

            s = src.translate(m, params);
            // don't share initial units
            s->pop_to_base_level();
            m_shared_units_prefix = s->get_assigned_literals().size();
            m_num_initial_atoms = s->get_num_bool_vars();
            // avoid preprocessing lemmas that are exchanged
            s->set_preprocess(false);

            for (expr* a : src_asms)
                asms.push_back(m_g2l(a));

            LOG_WORKER(1, " created with " << asms.size() << " assumptions\n");
        }

        void run() {
            bool is_first_run = true;
            node_lease lease;
            expr_ref_vector cube(m);

            while (true) {
                if (!b.get_cube(m_g2l, id, cube, is_first_run, lease)) {
                    LOG_WORKER(1, " no more cubes\n");
                    return;
                }
                is_first_run = false;
                collect_shared_clauses();
            check_cube_start:
                LOG_WORKER(1, " CUBE SIZE IN MAIN LOOP: " << cube.size() << "\n");
                if (m_config.m_global_backbones) {
                    bb_candidates local_candidates = find_backbone_candidates(cube);
                    b.collect_backbone_candidates(m_l2g, local_candidates);
                    bool lease_canceled = false;
                    if (!b.checkpoint_worker(id, lease, lease_canceled))
                        return;
                    if (lease_canceled) {
                        LOG_WORKER(1, " abandoning canceled lease\n");
                        continue;
                    }
                }
                lbool r = check_cube(cube);

                bool lease_canceled = false;
                if (!b.checkpoint_worker(id, lease, lease_canceled))
                    return;
                if (lease_canceled) {
                    LOG_WORKER(1, " abandoning canceled lease\n");
                    continue;
                }

                switch (r) {

                case l_undef: {
                    update_max_thread_conflicts();
                    LOG_WORKER(1, " found undef cube\n");
                    if (m_config.m_max_cube_depth <= cube.size())
                        goto check_cube_start;
                    expr_ref atom = get_split_atom(lease, cube);
                    if (atom) {
                        b.try_split(m_l2g, id, lease, atom.get(), m_config.m_threads_max_conflicts);
                    }
                    else {
                        goto check_cube_start;
                    }
                    break;
                }

                case l_true: {
                    LOG_WORKER(1, " found sat cube\n");
                    model_ref mdl;
                    s->get_model(mdl);
                    if (mdl)
                        b.set_sat(m_l2g, *mdl);
                    return;
                }

                case l_false: {
                    expr_ref_vector unsat_core(m);
                    s->get_unsat_core(unsat_core);
                    LOG_WORKER(2, " unsat core:\n";
                               for (auto c : unsat_core) verbose_stream() << mk_bounded_pp(c, m, 3) << "\n");

                    if (all_of(unsat_core, [&](expr* e) { return asms.contains(e); })) {
                        LOG_WORKER(1, " determined formula unsat\n");
                        b.set_unsat(m_l2g, unsat_core);
                        return;
                    }

                    LOG_WORKER(1, " found unsat cube\n");
                    auto* source = lease.leased_node;
                    expr_ref_vector const& core_to_use = m_config.m_ablate_backtracking ? cube : unsat_core;
                    b.backtrack(m_l2g, id, core_to_use, lease);

                    if (m_config.m_core_minimize)
                        b.enqueue_core_minimization(m_l2g, source, unsat_core);

                    if (m_config.m_share_conflicts)
                        b.collect_clause(m_l2g, id, mk_not(mk_and(unsat_core)));
                    break;
                }

                }
                if (m_config.m_share_units)
                    share_units();
            }
        }

        void cancel() {
            LOG_WORKER(1, " canceling\n");
            m.limit().cancel();
        }

        void cancel_lease() {
            LOG_WORKER(1, " canceling lease\n");
            m.limit().inc_cancel();
        }

        void collect_statistics(statistics& st) const {
            s->collect_statistics(st);
        }

        reslimit& limit() { return m.limit(); }
    };

    class backbones_worker {
    private:
        struct stats {
            unsigned m_batches_total = 0;
            unsigned m_candidates_total = 0;
            unsigned m_singleton_backbones = 0;
            unsigned m_backbones_detected = 0;
            unsigned m_internal_backbones_found = 0;
            unsigned m_retry_backbones_found = 0;
            unsigned m_bb_retries = 0;
            unsigned m_fallback_singleton_checks = 0;
            unsigned m_fallback_reason_chunk_exhausted = 0;
            unsigned m_fallback_reason_undef = 0;
            unsigned m_core_refinement_rounds = 0;
            unsigned m_lits_removed_by_core = 0;
            unsigned m_num_chunk_increases = 0;
        };

        unsigned         id;
        batch_manager&   b;
        ast_manager      m;
        ref<solver>      s;
        expr_ref_vector  asms;
        ast_translation  m_g2l, m_l2g;
        unsigned         m_bb_chunk_size = 20;
        unsigned         m_bb_conflicts_per_chunk = 1000;
        unsigned         m_shared_clause_limit = 0;
        stats            m_stats;
        unsigned         m_shared_units_prefix = 0;
        unsigned         m_num_initial_atoms = 0;
        bool             m_positive_mode = false;

        void collect_shared_clauses() {
            expr_ref_vector nc = b.return_shared_clauses(m_g2l, m_shared_clause_limit, UINT_MAX);
            for (expr* e : nc) {
                s->assert_expr(e);
                LOG_BB_WORKER(4, " asserting shared clause: " << mk_bounded_pp(e, m, 3) << "\n");
            }
        }

        bool try_get_unit_backbone(expr* candidate, expr_ref& backbone) {
            expr_ref_vector trail = s->get_assigned_literals();
            expr* atom = candidate;
            m.is_not(candidate, atom);
            for (expr* e : trail) {
                if (s->get_assign_level(e) > 0)
                    continue;
                expr* trail_atom = e;
                m.is_not(e, trail_atom);
                if (trail_atom != atom)
                    continue;
                backbone = expr_ref(e, m);
                return true;
            }
            return false;
        }

        lbool probe_literal(expr* e, bool is_retry) {
            lbool r = l_undef;
            try {
                asms.push_back(e);
                r = s->check_sat(asms);
                asms.pop_back();
            }
            catch (z3_error& err) {
                asms.pop_back();
                if (!m.limit().is_canceled())
                    b.set_exception(err.error_code());
            }
            catch (z3_exception& ex) {
                asms.pop_back();
                if (!m.limit().is_canceled() && !is_cancellation_exception(ex.what()))
                    b.set_exception(ex.what());
            }

            if (r == l_false) {
                expr_ref_vector core(m);
                s->get_unsat_core(core);
                if (!core.contains(e)) {
                    b.set_unsat(m_l2g, core);
                    return l_false;
                }
                expr_ref bb(mk_not(m, e), m);
                ++m_stats.m_backbones_detected;
                if (b.collect_global_backbone(m_l2g, bb)) {
                    ++m_stats.m_internal_backbones_found;
                    if (is_retry)
                        ++m_stats.m_retry_backbones_found;
                }
                s->assert_expr(bb.get());
                return l_undef;
            }
            if (r == l_true) {
                model_ref mdl;
                s->get_model(mdl);
                if (mdl)
                    b.set_sat(m_l2g, *mdl);
            }
            return r;
        }

        void run_batch_mode() {
            bb_candidates curr_batch;

            while (m.inc()) {
                if (!b.wait_for_backbone_job(id, m_g2l, curr_batch, m.limit())) {
                    LOG_BB_WORKER(1, " BACKBONES WORKER cancelling\n");
                    return;
                }

                if (curr_batch.empty())
                    continue;

                LOG_BB_WORKER(1, " received batch of " << curr_batch.size() << " candidates\n");
                collect_shared_clauses();

                unsigned local_cancel_epoch = b.get_cancel_epoch();
                auto canceled = [&] { return local_cancel_epoch != b.get_cancel_epoch(); };
                unsigned bb_candidate_epoch = b.get_bb_candidate_epoch();

                auto fallback_failed_literal_probe =
                    [&](expr_ref_vector const& chunk_lits, expr_ref_vector& bb_candidate_lits, bool is_retry = false) {
                        if (is_retry)
                            ++m_stats.m_bb_retries;
                        else
                            ++m_stats.m_fallback_singleton_checks;

                        unsigned old_max_conflicts = s->get_max_conflicts();
                        s->set_max_conflicts(10);

                        for (expr* lit : chunk_lits) {
                            if (is_retry && b.has_new_backbone_candidates(bb_candidate_epoch)) {
                                s->set_max_conflicts(old_max_conflicts);
                                return;
                            }
                            if (!m.inc() || canceled()) {
                                s->set_max_conflicts(old_max_conflicts);
                                return;
                            }
                            if (!bb_candidate_lits.contains(lit))
                                continue;

                            expr_ref bb_ref(lit, m);
                            if (m_positive_mode)
                                bb_ref = mk_not(m, bb_ref);

                            if (!b.is_global_backbone_or_negation(m_l2g, bb_ref.get())) {
                                expr_ref backbone(m);
                                if (try_get_unit_backbone(bb_ref.get(), backbone)) {
                                    ++m_stats.m_backbones_detected;
                                    if (b.collect_global_backbone(m_l2g, backbone)) {
                                        ++m_stats.m_internal_backbones_found;
                                        if (is_retry)
                                            ++m_stats.m_retry_backbones_found;
                                    }
                                    LOG_BB_WORKER(1, " fallback found unit backbone: " << mk_bounded_pp(backbone.get(), m, 3) << "\n");
                                }
                                else {
                                    expr* atom = bb_ref.get();
                                    m.is_not(bb_ref.get(), atom);
                                    if (s->get_bool_var(atom) != UINT_MAX) {
                                        lbool terminal_result = probe_literal(mk_not(m, bb_ref), is_retry);
                                        LOG_BB_WORKER(1, " RESULT: " << terminal_result << " FOR CANDIDATE: " << mk_bounded_pp(bb_ref.get(), m, 3) << "\n");
                                        if (terminal_result != l_undef) {
                                            s->set_max_conflicts(old_max_conflicts);
                                            return;
                                        }
                                    }
                                }
                            }
                            bb_candidate_lits.erase(lit);
                        }

                        s->set_max_conflicts(old_max_conflicts);
                    };

                ++m_stats.m_batches_total;
                m_stats.m_candidates_total += curr_batch.size();

                expr_ref_vector bb_candidate_lits(m);
                for (auto const& c : curr_batch)
                    bb_candidate_lits.push_back(c.lit);

                unsigned chunk_delta = 1;

                while (!bb_candidate_lits.empty() && !canceled() && m.inc()) {
                    {
                        unsigned j = 0;
                        for (expr* lit : bb_candidate_lits) {
                            if (!b.is_global_backbone_or_negation(m_l2g, lit))
                                bb_candidate_lits[j++] = lit;
                        }
                        bb_candidate_lits.shrink(j);
                    }

                    {
                        unsigned j = 0;
                        for (expr* lit : bb_candidate_lits) {
                            expr_ref backbone(m);
                            if (try_get_unit_backbone(lit, backbone)) {
                                if (b.collect_global_backbone(m_l2g, backbone))
                                    ++m_stats.m_internal_backbones_found;
                                ++m_stats.m_backbones_detected;
                                continue;
                            }
                            bb_candidate_lits[j++] = lit;
                        }
                        bb_candidate_lits.shrink(j);
                    }

                    unsigned chunk_size = std::min(m_bb_chunk_size * chunk_delta, bb_candidate_lits.size());
                    expr_ref_vector chunk_lits(m);
                    expr_ref_vector negated_chunk_lits(m);
                    expr_mark chunk_atoms;

                    for (unsigned i = 0; i < bb_candidate_lits.size() && chunk_lits.size() < chunk_size; ++i) {
                        expr* lit = bb_candidate_lits.get(i);
                        expr* atom = lit;
                        m.is_not(lit, atom);
                        if (chunk_atoms.is_marked(atom))
                            continue;
                        chunk_atoms.mark(atom);
                        chunk_lits.push_back(lit);
                        negated_chunk_lits.push_back(mk_not(m, lit));
                    }

                    expr_ref_vector bb_asms(m);
                    if (!m_positive_mode)
                        bb_asms.append(negated_chunk_lits);
                    else
                        bb_asms.append(chunk_lits);

                    collect_shared_clauses();

                    while (true) {
                        if (!m.inc()) {
                            b.set_canceled();
                            return;
                        }
                        if (canceled())
                            break;

                        ++m_stats.m_core_refinement_rounds;
                        unsigned base_asms_sz = asms.size();
                        for (expr* a : bb_asms)
                            asms.push_back(a);

                        s->set_max_conflicts(m_bb_conflicts_per_chunk);
                        lbool r = l_undef;
                        try {
                            r = s->check_sat(asms);
                        }
                        catch (z3_error& err) {
                            if (!m.limit().is_canceled())
                                b.set_exception(err.error_code());
                        }
                        catch (z3_exception& ex) {
                            if (!m.limit().is_canceled() && !is_cancellation_exception(ex.what()))
                                b.set_exception(ex.what());
                        }
                        asms.shrink(base_asms_sz);

                        if (!m.inc() || canceled())
                            break;

                        if (r == l_undef) {
                            LOG_BB_WORKER(1, " UNDEF at chunk_size=" << chunk_size << "\n");
                            if (chunk_size < bb_candidate_lits.size()) {
                                ++chunk_delta;
                                ++m_stats.m_num_chunk_increases;
                                break;
                            }

                            LOG_BB_WORKER(1, " UNDEF and max chunk -> fallback\n");
                            fallback_failed_literal_probe(chunk_lits, bb_candidate_lits);
                            ++m_stats.m_fallback_reason_undef;
                            chunk_delta = 1;
                            break;
                        }

                        if (r == l_true) {
                            LOG_BB_WORKER(1, " batch check returned SAT, thus entire formula is SAT\n");
                            model_ref mdl;
                            s->get_model(mdl);
                            if (mdl)
                                b.set_sat(m_l2g, *mdl);
                            curr_batch.reset();
                            return;
                        }

                        expr_ref_vector bb_asms_in_core(m);
                        expr_ref_vector unsat_core(m);
                        s->get_unsat_core(unsat_core);

                        for (expr* a : unsat_core)
                            if (bb_asms.contains(a))
                                bb_asms_in_core.push_back(a);

                        if (bb_asms_in_core.empty()) {
                            b.set_unsat(m_l2g, unsat_core);
                            return;
                        }

                        if (bb_asms_in_core.size() == 1) {
                            expr* a = bb_asms_in_core.back();
                            expr_ref backbone_lit(mk_not(m, a), m);

                            ++m_stats.m_singleton_backbones;
                            ++m_stats.m_backbones_detected;

                            if (b.collect_global_backbone(m_l2g, backbone_lit)) {
                                ++m_stats.m_internal_backbones_found;
                                s->assert_expr(backbone_lit.get());
                            }

                            expr* candidate_to_remove =
                                (!m_positive_mode) ? backbone_lit.get() : a;
                            bb_candidate_lits.erase(candidate_to_remove);
                        }

                        unsigned sz_before = bb_asms.size();
                        for (expr* a : bb_asms_in_core)
                            bb_asms.erase(a);
                        m_stats.m_lits_removed_by_core += sz_before - bb_asms.size();
                        chunk_delta = 1;

                        if (bb_asms.empty()) {
                            LOG_BB_WORKER(1, " no more negated chunk literals, fallback to individual checks\n");
                            fallback_failed_literal_probe(chunk_lits, bb_candidate_lits);
                            ++m_stats.m_fallback_reason_chunk_exhausted;
                            break;
                        }
                    }
                }

                while (!b.has_new_backbone_candidates(bb_candidate_epoch) && !canceled() && m.inc()) {
                    collect_shared_clauses();
                    unsigned found_before = m_stats.m_internal_backbones_found;

                    expr_ref_vector bb_snapshot = b.get_global_backbones_snapshot(m_g2l);
                    expr_mark bb_mark;
                    for (expr* e : bb_snapshot) {
                        bb_mark.mark(e);
                        bb_mark.mark(mk_not(m, e));
                    }
                    bb_candidate_lits.reset();
                    for (auto const& c : curr_batch)
                        if (!bb_mark.is_marked(c.lit.get()))
                            bb_candidate_lits.push_back(c.lit);

                    if (bb_candidate_lits.empty())
                        break;

                    fallback_failed_literal_probe(bb_candidate_lits, bb_candidate_lits, true);

                    if (m_stats.m_internal_backbones_found == found_before)
                        break;
                }

                if (!canceled())
                    b.cancel_current_backbone_batch();

                curr_batch.reset();
            }
        }

    public:
        backbones_worker(unsigned id, parallel_solver& p, solver& src, params_ref const& params,
                         expr_ref_vector const& src_asms)
            : id(id), b(p.m_batch_manager),
              asms(m), m_g2l(src.get_manager(), m), m_l2g(m, src.get_manager()) {
            s = src.translate(m, params);
            s->set_max_conflicts(m_bb_conflicts_per_chunk);
            s->pop_to_base_level();
            for (expr* a : src_asms)
                asms.push_back(m_g2l(a));
            m_positive_mode = id != 0;
            m_shared_units_prefix = s->get_assigned_literals().size();
            m_num_initial_atoms = s->get_num_bool_vars();
            IF_VERBOSE(1, verbose_stream() << "Initialized backbones thread " << id << "\n");
        }

        void run() { run_batch_mode(); }

        void cancel() {
            LOG_BB_WORKER(1, " BACKBONES WORKER cancelling\n");
            m.limit().cancel();
        }

        void collect_statistics(statistics& st) const {
            st.update("parallel-bb-batches-total", m_stats.m_batches_total);
            st.update("parallel-bb-candidates-total", m_stats.m_candidates_total);
            st.update("parallel-bb-backbones-detected", m_stats.m_backbones_detected);
            st.update("parallel-bb-internal-backbones-found", m_stats.m_internal_backbones_found);
            st.update("parallel-bb-retry-backbones-found", m_stats.m_retry_backbones_found);
            st.update("parallel-bb-retries", m_stats.m_bb_retries);
            st.update("parallel-bb-core-refinement-rounds", m_stats.m_core_refinement_rounds);
            st.update("parallel-bb-singleton-backbones", m_stats.m_singleton_backbones);
            st.update("parallel-bb-fallback-singleton-checks", m_stats.m_fallback_singleton_checks);
            st.update("parallel-bb-fallback-chunk-exhausted", m_stats.m_fallback_reason_chunk_exhausted);
            st.update("parallel-bb-fallback-undef", m_stats.m_fallback_reason_undef);
            st.update("parallel-bb-literals-removed-by-core", m_stats.m_lits_removed_by_core);
            st.update("parallel-bb-num-chunk-increases", m_stats.m_num_chunk_increases);

            auto safe_ratio = [](double num, double den) -> double {
                return den > 0 ? num / den : 0.0;
            };

            st.update("parallel-bb-backbone-yield-pct",
                100.0 * safe_ratio(m_stats.m_internal_backbones_found, m_stats.m_candidates_total));
            st.update("parallel-bb-avg-backbones-per-batch",
                safe_ratio(m_stats.m_internal_backbones_found, m_stats.m_batches_total));
            st.update("parallel-bb-core-refinement-rounds-per-batch",
                safe_ratio(m_stats.m_core_refinement_rounds, m_stats.m_batches_total));
            st.update("parallel-bb-core-effectiveness-lit-removed-per-round",
                safe_ratio(m_stats.m_lits_removed_by_core, m_stats.m_core_refinement_rounds));
        }

        reslimit& limit() { return m.limit(); }
    };

    class core_minimizer_worker {
        batch_manager&   b;
        ast_manager      m;
        ref<solver>      s;
        expr_ref_vector  asms;
        ast_translation  m_g2l, m_l2g;
        unsigned         m_num_core_minimize_calls = 0;
        unsigned         m_num_core_minimize_undef = 0;
        unsigned         m_num_core_minimize_refined = 0;
        unsigned         m_num_core_minimize_lits_removed = 0;
        unsigned         m_num_core_minimize_found_sat = 0;
        unsigned         m_core_minimize_conflict_budget = 5000;
        unsigned         m_shared_clause_limit = 0;

        void collect_shared_clauses() {
            expr_ref_vector nc = b.return_shared_clauses(m_g2l, m_shared_clause_limit, UINT_MAX);
            for (expr* e : nc) {
                s->assert_expr(e);
                IF_VERBOSE(4, verbose_stream() << "Core minimizer asserting shared clause: "
                                               << mk_bounded_pp(e, m, 3) << "\n";);
            }
        }

        void minimize_unsat_core(expr_ref_vector& core) {
            expr_ref_vector unknown(core), mus(m), trial(m);
            unsigned original_size = core.size();
            ++m_num_core_minimize_calls;

            while (!unknown.empty()) {
                if (!m.inc()) {
                    core.reset();
                    core.append(mus);
                    core.append(unknown);
                    return;
                }

                expr* lit = unknown.back();
                unknown.pop_back();
                expr_ref not_lit(mk_not(m, lit), m);

                trial.reset();
                trial.append(mus);
                trial.append(unknown);
                trial.push_back(not_lit);

                lbool r = l_undef;
                try {
                    s->set_max_conflicts(m_core_minimize_conflict_budget);
                    r = s->check_sat(trial);
                }
                catch (z3_error&) {
                    r = l_undef;
                }
                catch (z3_exception&) {
                    r = l_undef;
                }

                switch (r) {
                case l_undef:
                    ++m_num_core_minimize_undef;
                    mus.push_back(lit);
                    break;
                case l_true: {
                    if (!asms.empty()) {
                        mus.push_back(lit);
                        break;
                    }
                    ++m_num_core_minimize_found_sat;
                    model_ref mdl;
                    s->get_model(mdl);
                    if (mdl)
                        b.set_sat(m_l2g, *mdl);
                    return;
                }
                case l_false: {
                    expr_ref_vector unsat_core(m);
                    s->get_unsat_core(unsat_core);
                    if (!unsat_core.contains(not_lit)) {
                        ++m_num_core_minimize_refined;
                        unknown.reset();
                        expr_ref_vector new_mus(m);
                        for (expr* c : unsat_core) {
                            if (mus.contains(c))
                                new_mus.push_back(c);
                            else
                                unknown.push_back(c);
                        }
                        mus.reset();
                        mus.append(new_mus);
                    }
                    break;
                }
                default:
                    UNREACHABLE();
                }
            }

            core.reset();
            core.append(mus);
            core.append(unknown);
            if (core.size() < original_size)
                m_num_core_minimize_lits_removed += original_size - core.size();
        }

    public:
        core_minimizer_worker(parallel_solver& p, solver& src, params_ref const& params,
                              expr_ref_vector const& src_asms)
            : b(p.m_batch_manager),
              asms(m), m_g2l(src.get_manager(), m), m_l2g(m, src.get_manager()) {
            s = src.translate(m, params);
            s->pop_to_base_level();
            // avoid preprocessing lemmas that are exchanged
            s->set_preprocess(false);
            for (expr* a : src_asms)
                asms.push_back(m_g2l(a));
            IF_VERBOSE(1, verbose_stream() << "Initialized core minimizer thread\n");
        }

        void run() {
            while (m.inc()) {
                search_tree::node<solver_cube_config>* source = nullptr;
                expr_ref_vector core(m);
                if (!b.wait_for_core_min_job(m_g2l, source, core, m.limit()))
                    return;

                unsigned original_size = core.size();
                if (original_size <= 1)
                    continue;

                collect_shared_clauses();

                expr_ref_vector minimized(m);
                minimized.append(core);

                if (minimized.size() <= 1)
                    continue;

                minimize_unsat_core(minimized);

                if (minimized.size() < original_size)
                    b.publish_minimized_core(m_l2g, asms, source, original_size, minimized);
            }
            b.set_canceled();
        }

        void cancel() {
            IF_VERBOSE(1, verbose_stream() << "Core minimizer cancelling\n");
            m.limit().cancel();
        }

        void collect_statistics(statistics& st) const {
            st.update("parallel-core-minimize-calls", m_num_core_minimize_calls);
            st.update("parallel-core-minimize-undef", m_num_core_minimize_undef);
            st.update("parallel-core-minimize-refined", m_num_core_minimize_refined);
            st.update("parallel-core-minimize-lits-removed", m_num_core_minimize_lits_removed);
            st.update("parallel-core-minimize-found-sat", m_num_core_minimize_found_sat);
        }

        reslimit& limit() { return m.limit(); }
    };

    /* ---- members ---- */
    ref<solver>               m_solver;
    ast_manager&              m_manager;
    params_ref                m_params;
    scoped_ptr_vector<worker> m_workers;
    scoped_ptr<core_minimizer_worker> m_core_minimizer_worker;
    scoped_ptr_vector<backbones_worker> m_global_backbones_workers;
    batch_manager             m_batch_manager;
    statistics                m_stats;
public:

    parallel_solver(solver* s, params_ref const& p)
        : m_solver(s),
          m_manager(s->get_manager()),
          m_params(p),
          m_batch_manager(s->get_manager(), *this) {}

    params_ref mk_worker_params(unsigned seed_offset) const {
        params_ref p(m_params);
        // Match smt_parallel's per-worker m_smt_params.m_random_seed += id.
        // Generic solver workers receive the seed through translate params.
        unsigned base_seed = m_params.get_uint("random_seed", 0);
        p.set_uint("random_seed", base_seed + seed_offset);
        p.set_uint("threads", 1);
        return p;
    }

    /* Run the portfolio.  Returns sat/unsat/undef.
     *
     * On sat:   *mdl is populated (translated into m_manager).
     * On unsat: *core is populated (translated into m_manager).
     * asms:     original external assumptions (in m_manager). */
    lbool solve(expr_ref_vector const& asms,
                model_ref& mdl,
                expr_ref_vector& core) {

        parallel_params pp(m_params);
        unsigned num_threads = std::min(
            static_cast<unsigned>(std::thread::hardware_concurrency()),
            pp.threads_max());
        bool core_minimize = pp.core_minimize();
        unsigned num_bb_threads = pp.num_bb_threads();
        if (num_bb_threads > 2)
            throw default_exception("parallel.num_bb_threads must be 0, 1, or 2");
        unsigned total_threads = num_threads + (core_minimize ? 1 : 0) + num_bb_threads;

        IF_VERBOSE(1, verbose_stream() << "Parallel tactical2 with " << total_threads << " threads\n";);

        if (m_manager.has_trace_stream())
            throw default_exception(
                "parallel_tactic2 does not work with trace streams");

        /* Build workers – each gets a translated solver copy. */
        m_workers.reset();
        scoped_limits sl(m_manager.limit());

        // Set up the source before translating workers. SMT context copies
        // then run initial internalization/preprocessing before workers disable
        // preprocessing for exchanged lemmas.
        m_solver->setup_for_parallel();

        for (unsigned i = 0; i < num_threads; ++i) {
            params_ref worker_params = mk_worker_params(i);
            auto* w = alloc(worker, i, *this, *m_solver, worker_params, asms);
            m_workers.push_back(w);
            sl.push_child(&(w->limit()));
        }

        m_core_minimizer_worker = nullptr;
        if (core_minimize) {
            params_ref core_min_params = mk_worker_params(num_threads);
            m_core_minimizer_worker = alloc(core_minimizer_worker, *this, *m_solver, core_min_params, asms);
            sl.push_child(&(m_core_minimizer_worker->limit()));
        }
        m_global_backbones_workers.reset();
        for (unsigned i = 0; i < num_bb_threads; ++i) {
            params_ref bb_params = mk_worker_params(num_threads + (core_minimize ? 1 : 0) + i);
            auto* w = alloc(backbones_worker, i, *this, *m_solver, bb_params, asms);
            m_global_backbones_workers.push_back(w);
            sl.push_child(&(w->limit()));
        }
        IF_VERBOSE(1, verbose_stream() << "Launched " << m_workers.size() << " CDCL threads, "
                                       << 0 << " SLS threads, "
                                       << (m_core_minimizer_worker ? 1 : 0) << " core minimizer threads, "
                                       << m_global_backbones_workers.size() << " global backbone threads.\n";);

        m_batch_manager.initialize(num_bb_threads);

        auto safe_run = [&](auto&& run_fn, reslimit& lim) {
            try {
                run_fn();
                if (lim.is_canceled())
                    m_batch_manager.set_canceled();
            } catch (z3_error &err) {
                IF_VERBOSE(0, verbose_stream() << "Exception in parallel solver: " << err.what() << "\n");
                if (!lim.is_canceled())
                    m_batch_manager.set_exception(err.error_code());
                else
                    m_batch_manager.set_canceled();
            } catch (z3_exception &ex) {
                IF_VERBOSE(0, verbose_stream() << "Exception in parallel solver: " << ex.what() << "\n");
                if (!lim.is_canceled() && !is_cancellation_exception(ex.what()))
                    m_batch_manager.set_exception(ex.what());
                else
                    m_batch_manager.set_canceled();
            } catch (...) {
                IF_VERBOSE(0, verbose_stream() << "Unknown exception in parallel solver\n");
                if (!lim.is_canceled())
                    m_batch_manager.set_exception("unknown exception");
                else
                    m_batch_manager.set_canceled();
            }
        };

        /* Launch threads. */
        vector<std::thread> threads;
        for (auto *w : m_workers)
            threads.push_back(std::thread([w, &safe_run]() {
                safe_run([w]() { w->run(); }, w->limit());
            }));
        if (m_core_minimizer_worker)
            threads.push_back(std::thread([this, &safe_run]() {
                safe_run([this]() { m_core_minimizer_worker->run(); }, m_core_minimizer_worker->limit());
            }));
        for (auto* w : m_global_backbones_workers)
            threads.push_back(std::thread([w, &safe_run]() {
                safe_run([w]() { w->run(); }, w->limit());
            }));

        for (auto& t : threads)
            t.join();

        m_solver->reset_statistics();
        statistics aux;
        for (auto* w : m_workers) {
            aux.reset();
            w->collect_statistics(aux);
            m_solver->add_statistics(aux);
        }
        aux.reset();
        m_batch_manager.collect_statistics(aux);
        m_solver->add_statistics(aux);
        if (m_core_minimizer_worker) {
            aux.reset();
            m_core_minimizer_worker->collect_statistics(aux);
            m_solver->add_statistics(aux);
        }
        for (auto* w : m_global_backbones_workers) {
            aux.reset();
            w->collect_statistics(aux);
            m_solver->add_statistics(aux);
        }
        m_stats.reset();
        m_solver->collect_statistics(m_stats);

        m_manager.limit().reset_cancel();

        lbool result = m_batch_manager.get_result();

        if (result == l_true)
            mdl = m_batch_manager.get_model();

        if (result == l_false) {
            for (expr* c : m_batch_manager.get_unsat_core())
                core.push_back(c);
        }

        sl.reset();
        m_workers.reset();
        m_core_minimizer_worker = nullptr;
        m_global_backbones_workers.reset();
        return result;
    }

    void collect_statistics(statistics& st) const {
        st.copy(m_stats);
    }

    void reset_statistics() {
        m_stats.reset();
    }
};

/* ------------------------------------------------------------------ */
/* parallel_tactic2 – wraps parallel_solver as a tactic               */
/* ------------------------------------------------------------------ */

class parallel_tactic2 : public tactic {

    solver_ref  m_solver;
    ast_manager& m_manager;
    params_ref   m_params;
    statistics   m_stats;

public:

    parallel_tactic2(solver* s, params_ref const& p)
        : m_solver(s), m_manager(s->get_manager()), m_params(p) {}

    char const* name() const override { return "parallel_tactic2"; }

    void operator()(const goal_ref& g, goal_ref_buffer& result) override {
        fail_if_proof_generation("parallel_tactic2", g);
        ast_manager& m = g->m();

        if (m.has_trace_stream())
            throw default_exception(
                "parallel_tactic2 does not work with trace streams");

        /* Translate goal into a set of clauses + assumptions. */
        solver* s = m_solver->translate(m, m_params);
        expr_ref_vector clauses(m);
        ptr_vector<expr> assumptions_raw;
        obj_map<expr, expr*> bool2dep;
        ref<generic_model_converter> fmc;
        extract_clauses_and_dependencies(g, clauses, assumptions_raw, bool2dep, fmc);
        for (expr* cl : clauses)
            s->assert_expr(cl);

        expr_ref_vector asms(m);
        asms.append(assumptions_raw.size(), assumptions_raw.data());

        parallel_solver ps(s, m_params);

        model_ref mdl;
        expr_ref_vector core(m);
        lbool is_sat = ps.solve(asms, mdl, core);

        ps.collect_statistics(m_stats);

        switch (is_sat) {
        case l_true: {
            if (g->models_enabled() && mdl) {
                model_converter_ref mc = model2model_converter(mdl.get());
                mc = concat(fmc.get(), mc.get());
                mc = concat(s->mc0(), mc.get());
                g->add(mc.get());
            }
            g->reset();
            break;
        }

        case l_false: {
            SASSERT(!g->proofs_enabled());
            expr_dependency* lcore = nullptr;
            proof* pr = nullptr;
            if (!core.empty()) {
                for (expr* c : core) {
                    expr* dep = nullptr;
                    if (bool2dep.find(c, dep))
                        lcore = m.mk_join(lcore, m.mk_leaf(dep));
                }
            }
            g->assert_expr(m.mk_false(), pr, lcore);
            break;
        }

        case l_undef:
            if (!m.inc())
                throw tactic_exception(Z3_CANCELED_MSG);
            break;
        }

        result.push_back(g.get());
    }

    void cleanup() override {}

    tactic* translate(ast_manager& m) override {
        solver* s = m_solver->translate(m, m_params);
        return alloc(parallel_tactic2, s, m_params);
    }

    void updt_params(params_ref const& p) override {
        m_params.copy(p);
    }

    void collect_statistics(statistics& st) const override {
        st.copy(m_stats);
    }

    void reset_statistics() override {
        m_stats.reset();
    }
};

tactic* mk_parallel_tactic2(solver* s, params_ref const& p) {
    return alloc(parallel_tactic2, s, p);
}

#endif
