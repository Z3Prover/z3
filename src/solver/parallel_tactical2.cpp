/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    parallel_tactical2.cpp

Abstract:

    Parallel portfolio solver using the solver API.

    Models the internals after smt/smt_parallel.cpp but operates on generic
    solver objects (smt_solver, inc_sat_solver, etc.) via the solver interface
    instead of accessing smt::context internals directly.

    Key features compared to parallel_tactical.cpp:
      - Search tree for coordinated non-chronological backtracking (from smt_parallel).
      - Shared clause pool: learned conflict clauses are broadcast to all workers.
      - Shared backbone/unit pool: base-level units propagated by one worker are
        asserted as facts on every other worker's solver.
      - Workers reuse their solver state across multiple cube checks, accumulating
        learned clauses (same pattern as smt_parallel workers).

    Key differences from smt_parallel:
      - Uses the solver API throughout (translate, check_sat, get_trail, cube,
        get_model, get_unsat_core, assert_expr, push, pop, updt_params, …)
        rather than accessing smt::context members directly.
      - Works with any conforming solver implementation.

    Cube path management follows the assumption-based pattern from smt_parallel:
      - The worker's solver base assertion set is fixed at construction (the full
        problem is translated into the worker's own ast_manager once).
      - Shared clauses discovered by other workers are appended to the base set via
        assert_expr at any time.
      - The current cube path is passed as extra assumptions on every check_sat call,
        so the solver can reuse learned clauses across different cube checks.

    Split atom selection is performed by temporarily pushing the cube path onto
    the solver, calling solver::cube(), retrieving the first proposed literal, and
    then popping, so that the base state is preserved.

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
#include "solver/solver_preprocess.h"
#include "util/search_tree.h"
#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "solver/solver2tactic.h"

#include <cmath>
#include <mutex>

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

/* ------------------------------------------------------------------ */
/* Search-tree literal configuration                                    */
/* ------------------------------------------------------------------ */

struct solver_cube_config {
    using literal = expr_ref;
    static bool literal_is_null(expr_ref const& l) { return l == nullptr; }
    static std::ostream& display_literal(std::ostream& out, expr_ref const& l) {
        if (l) return out << mk_bounded_pp(l, l.get_manager());
        return out << "(null)";
    }
};

/* ------------------------------------------------------------------ */
/* parallel_solver – the core portfolio engine                         */
/* ------------------------------------------------------------------ */

class parallel_solver {

    /* ---- forward declarations ---- */
    class worker;

    /* ---- node lease (mirrors smt_parallel) ---- */
    struct node_lease {
        search_tree::node<solver_cube_config>* leased_node = nullptr;
        unsigned cancel_epoch = 0;
        bool cancel_signaled  = false;
    };

    /* ---- shared clause entry ---- */
    struct shared_clause {
        unsigned source_worker_id;
        expr_ref clause;
    };

    /* ================================================================
     * batch_manager
     * Coordinates workers: distributes cubes, collects clauses/units,
     * stores the final result (sat model / unsat core / exception).
     * ================================================================ */
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
        };

        ast_manager&   m;
        parallel_solver& p;
        std::mutex     mux;
        state          m_state = state::is_running;
        stats          m_stats;

        search_tree::tree<solver_cube_config> m_search_tree;
        vector<node_lease> m_worker_leases;

        /* shared clause pool (guarded by mux) */
        vector<shared_clause>    m_shared_clause_trail;
        obj_hashtable<expr>      m_shared_clause_set;

        /* shared backbone / unit pool (guarded by mux) */
        obj_hashtable<expr>      m_global_backbones;

        /* result storage (guarded by mux) */
        unsigned     m_exception_code = 0;
        std::string  m_exception_msg;
        model_ref    m_model;           /* sat model translated to m */
        expr_ref_vector m_unsat_core;   /* unsat core translated to m */

        /* ---- cancellation helpers (called under mux) ---- */
        void cancel_workers_unlocked() {
            IF_VERBOSE(1, verbose_stream() << "par2: canceling workers\n");
            for (auto* w : p.m_workers)
                w->cancel();
        }

        void release_lease_unlocked(unsigned worker_id,
                                    search_tree::node<solver_cube_config>* n) {
            if (worker_id >= m_worker_leases.size()) return;
            auto& lease = m_worker_leases[worker_id];
            if (!lease.leased_node || lease.leased_node != n) return;
            m_search_tree.dec_active_workers(lease.leased_node);
            lease = {};
        }

        void cancel_closed_leases_unlocked(unsigned source_worker_id) {
            unsigned n = std::min(m_worker_leases.size(), p.m_workers.size());
            for (unsigned id = 0; id < n; ++id) {
                if (id == source_worker_id) continue;
                auto const& lease = m_worker_leases[id];
                if (lease.leased_node && !lease.cancel_signaled &&
                    m_search_tree.is_lease_canceled(lease.leased_node, lease.cancel_epoch)) {
                    p.m_workers[id]->cancel_lease();
                    m_worker_leases[id].cancel_signaled = true;
                }
            }
        }

        void collect_clause_unlocked(ast_translation& l2g,
                                     unsigned source_worker_id,
                                     expr* clause) {
            expr* g_clause = l2g(clause);
            if (!m_shared_clause_set.contains(g_clause)) {
                m_shared_clause_set.insert(g_clause);
                shared_clause sc{source_worker_id, expr_ref(g_clause, m)};
                m_shared_clause_trail.push_back(std::move(sc));
            }
        }

        bool is_global_backbone_unlocked(ast_translation& l2g,
                                         expr* bb_cand) {
            expr_ref cand(l2g(bb_cand), m);
            return m_global_backbones.contains(cand.get());
        }

    public:

        batch_manager(ast_manager& m, parallel_solver& p)
            : m(m), p(p),
              m_search_tree(expr_ref(m)),
              m_unsat_core(m) {}

        /* ---- initialisation ---- */
        void initialize(unsigned num_workers,
                        unsigned initial_max_thread_conflicts = 1000) {
            m_state = state::is_running;
            m_search_tree.reset();
            m_search_tree.set_effort_unit(initial_max_thread_conflicts);
            m_worker_leases.reset();
            m_worker_leases.resize(num_workers);
            m_shared_clause_trail.reset();
            m_shared_clause_set.reset();
            m_global_backbones.reset();
            m_model = nullptr;
            m_unsat_core.reset();
        }

        /* ---- result setters (called by workers, guarded by mux) ---- */
        void set_sat(ast_translation& l2g, model& mdl) {
            std::scoped_lock lock(mux);
            IF_VERBOSE(1, verbose_stream() << "par2: batch_manager SAT\n");
            if (m_state != state::is_running) return;
            m_state = state::is_sat;
            m_model = mdl.translate(l2g);
            cancel_workers_unlocked();
        }

        void set_unsat(ast_translation& l2g,
                       expr_ref_vector const& core) {
            std::scoped_lock lock(mux);
            IF_VERBOSE(1, verbose_stream() << "par2: batch_manager UNSAT\n");
            if (m_state != state::is_running) return;
            m_state = state::is_unsat;
            SASSERT(m_unsat_core.empty());
            for (expr* c : core)
                m_unsat_core.push_back(l2g(c));
            cancel_workers_unlocked();
        }

        void set_exception(std::string const& msg) {
            std::scoped_lock lock(mux);
            IF_VERBOSE(1, verbose_stream() << "par2: batch_manager exception: " << msg << "\n");
            if (m_state != state::is_running) return;
            m_state = state::is_exception_msg;
            m_exception_msg = msg;
            cancel_workers_unlocked();
        }

        void set_exception(unsigned error_code) {
            std::scoped_lock lock(mux);
            if (m_state != state::is_running) return;
            m_state = state::is_exception_code;
            m_exception_code = error_code;
            cancel_workers_unlocked();
        }

        /* ---- cube distribution (called by workers) ---- */
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
            lease.cancel_epoch = t->get_cancel_epoch();
            if (id >= m_worker_leases.size())
                m_worker_leases.resize(id + 1);
            m_worker_leases[id] = lease;

            /* build cube from path root → t */
            for (auto* cur = t; cur; cur = cur->parent()) {
                if (solver_cube_config::literal_is_null(cur->get_literal()))
                    break;
                cube.push_back(expr_ref(g2l(cur->get_literal().get()), g2l.to()));
            }
            return true;
        }

        /* ---- backtrack on conflict (called by workers) ---- */
        void backtrack(ast_translation& l2g, unsigned worker_id,
                       expr_ref_vector const& core,
                       node_lease const& lease) {
            std::scoped_lock lock(mux);
            if (m_state != state::is_running) return;

            vector<solver_cube_config::literal> g_core;
            for (auto c : core)
                g_core.push_back(expr_ref(l2g(c), m));

            if (!m_search_tree.is_lease_canceled(
                    lease.leased_node, lease.cancel_epoch)) {
                release_lease_unlocked(worker_id, lease.leased_node);
                m_search_tree.backtrack(lease.leased_node, g_core);
            }

            cancel_closed_leases_unlocked(worker_id);

            IF_VERBOSE(2, m_search_tree.display(verbose_stream() << "\n"););

            if (m_search_tree.is_closed()) {
                IF_VERBOSE(1, verbose_stream() << "par2: search tree closed → UNSAT\n");
                m_state = state::is_unsat;
                for (auto& e : m_search_tree.get_core_from_root())
                    m_unsat_core.push_back(e.get());
                cancel_workers_unlocked();
            }
        }

        /* ---- try to split (called on undef) ---- */
        void try_split(ast_translation& l2g, unsigned worker_id,
                       node_lease const& lease,
                       expr* atom, unsigned effort) {
            std::scoped_lock lock(mux);
            if (m_state != state::is_running) return;
            if (m_search_tree.is_lease_canceled(
                    lease.leased_node, lease.cancel_epoch)) return;

            expr_ref lit(m), nlit(m);
            lit  = l2g(atom);
            nlit = mk_not(m, lit);

            bool did_split = m_search_tree.try_split(
                lease.leased_node, lease.cancel_epoch,
                lit, nlit, effort);

            release_lease_unlocked(worker_id, lease.leased_node);

            if (did_split) {
                ++m_stats.m_num_cubes;
                m_stats.m_max_cube_depth = std::max(
                    m_stats.m_max_cube_depth,
                    lease.leased_node->depth() + 1);
                IF_VERBOSE(1, verbose_stream() << "par2: split on "
                    << mk_bounded_pp(lit, m, 3) << "\n");
            }
        }

        void release_lease(unsigned worker_id, node_lease const& lease) {
            std::scoped_lock lock(mux);
            release_lease_unlocked(worker_id, lease.leased_node);
        }

        bool lease_canceled(node_lease const& lease) {
            std::scoped_lock lock(mux);
            return m_state == state::is_running &&
                   m_search_tree.is_lease_canceled(
                       lease.leased_node, lease.cancel_epoch);
        }

        /* ---- clause sharing ---- */
        void collect_clause(ast_translation& l2g,
                            unsigned source_worker_id,
                            expr* clause) {
            std::scoped_lock lock(mux);
            collect_clause_unlocked(l2g, source_worker_id, clause);
        }

        expr_ref_vector return_shared_clauses(ast_translation& g2l,
                                              unsigned& worker_limit,
                                              unsigned worker_id) {
            std::scoped_lock lock(mux);
            expr_ref_vector result(g2l.to());
            for (unsigned i = worker_limit; i < m_shared_clause_trail.size(); ++i) {
                if (m_shared_clause_trail[i].source_worker_id != worker_id)
                    result.push_back(g2l(m_shared_clause_trail[i].clause.get()));
            }
            worker_limit = m_shared_clause_trail.size();
            return result;
        }

        /* ---- backbone / unit sharing ---- */
        bool collect_global_backbone(ast_translation& l2g,
                                     expr_ref const& backbone,
                                     unsigned source_worker_id = UINT_MAX) {
            std::scoped_lock lock(mux);
            if (is_global_backbone_unlocked(l2g, backbone.get()))
                return false;
            expr_ref g_bb(l2g(backbone.get()), m);
            m_global_backbones.insert(g_bb.get());
            ++m_stats.m_backbones_found;
            IF_VERBOSE(2, verbose_stream() << "par2: new backbone "
                << mk_bounded_pp(g_bb, m, 3) << "\n");
            /* share it as a unit clause so other workers pick it up */
            collect_clause_unlocked(l2g, source_worker_id, backbone.get());
            return true;
        }

        /* ---- result accessors ---- */
        lbool get_result() const {
            if (m.limit().is_canceled()) return l_undef;
            switch (m_state) {
            case state::is_running:
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
            st.update("par2-cubes",       m_stats.m_num_cubes);
            st.update("par2-cube-depth",  m_stats.m_max_cube_depth);
            st.update("par2-backbones",   m_stats.m_backbones_found);
        }
    }; // class batch_manager

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
            unsigned m_max_cube_depth        = 20;
        };

        unsigned         id;
        batch_manager&   b;
        ast_manager      m;                 /* worker-local manager */
        ref<solver>      s;                 /* translated solver copy */
        expr_ref_vector  asms;              /* translated assumptions */
        ast_translation  m_g2l, m_l2g;     /* global↔local translations */
        config           m_config;
        expr_mark        m_known_units;     /* units already shared by this worker */
        unsigned         m_shared_clause_limit = 0;

        void update_max_conflicts() {
            m_config.m_threads_max_conflicts = static_cast<unsigned>(
                m_config.m_max_conflict_mul * m_config.m_threads_max_conflicts);
            /* cap at the configured global maximum to prevent runaway cube checks */
            if (m_config.m_threads_max_conflicts > m_config.m_max_conflicts)
                m_config.m_threads_max_conflicts = m_config.m_max_conflicts;
        }

        /* Check the current cube (passed as additional assumptions).
         * The solver's conflict budget is set via updt_params before
         * each call so that long-running cubes are interrupted. */
        lbool check_cube(expr_ref_vector const& cube) {
            params_ref p;
            p.set_uint("max_conflicts",
                       std::min(m_config.m_threads_max_conflicts,
                                m_config.m_max_conflicts));
            s->updt_params(p);

            expr_ref_vector combined(m);
            combined.append(asms);
            combined.append(cube);

            IF_VERBOSE(2, verbose_stream() << "par2 worker " << id
                << ": checking cube of size " << cube.size() << "\n");
            lbool r = l_undef;
            try {
                r = s->check_sat(combined);
            }
            catch (z3_error& err) {
                if (!m.limit().is_canceled())
                    b.set_exception(err.error_code());
            }
            catch (z3_exception& ex) {
                if (!m.limit().is_canceled())
                    b.set_exception(ex.what());
            }
            IF_VERBOSE(2, verbose_stream() << "par2 worker " << id
                << ": cube result " << r << "\n");
            return r;
        }

        /* Assert shared clauses discovered by other workers into the
         * base assertion set of this worker's solver.  The solver
         * automatically re-uses them on the next check_sat call. */
        void collect_shared_clauses() {
            expr_ref_vector nc = b.return_shared_clauses(
                m_g2l, m_shared_clause_limit, id);
            for (expr* e : nc) {
                IF_VERBOSE(4, verbose_stream() << "par2 worker " << id
                    << ": asserting shared clause "
                    << mk_bounded_pp(e, m, 3) << "\n");
                s->assert_expr(e);
            }
        }

        /* Propagate any new base-level units (backbone literals) this
         * worker has learned to the shared backbone pool.
         *
         * Uses solver::get_trail(0) which returns all literals
         * propagated at decision level 0. */
        void share_units() {
            if (!m_config.m_share_units) return;
            expr_ref_vector trail = s->get_trail(0);
            for (expr* e : trail) {
                /* get_trail may include ground terms; skip complex ones */
                expr* atom = e;
                m.is_not(e, atom);
                if (!is_uninterp_const(atom)) continue;
                if (m_known_units.is_marked(e)) continue;
                m_known_units.mark(e);
                expr_ref lit(e, m);
                b.collect_global_backbone(m_l2g, lit, id);
            }
        }

        /* Select a split atom using solver::cube() on a temporary
         * solver state that includes the current cube path.
         *
         * We push the cube literals, call cube(), take the first
         * literal, then pop to restore the base state. */
        expr_ref get_split_atom(expr_ref_vector const& cube) {
            if (cube.size() >= m_config.m_max_cube_depth)
                return expr_ref(nullptr, m);

            s->push();
            for (expr* c : cube)
                s->assert_expr(c);

            expr_ref_vector vars(m);
            expr_ref_vector c = s->cube(vars, UINT_MAX);

            s->pop(1);

            /* solver::cube() convention: an empty result means done; a result
             * whose last element is true means the problem is trivially sat;
             * a result whose last element is false means unsat was detected.
             * In all other cases every element (including index 0) is a
             * valid literal that can serve as a split atom. */
            if (c.empty() || m.is_true(c.back()) || m.is_false(c.back()))
                return expr_ref(nullptr, m);

            return expr_ref(c.get(0), m);
        }

    public:

        worker(unsigned id, parallel_solver& p,
               solver& src, params_ref const& params,
               expr_ref_vector const& src_asms)
            : id(id), b(p.m_batch_manager),
              asms(m), m_g2l(src.get_manager(), m), m_l2g(m, src.get_manager())
        {
            /* create translated solver copy */
            s = src.translate(m, params);

            /* translate assumptions */
            for (expr* a : src_asms)
                asms.push_back(m_g2l(a));

            IF_VERBOSE(1, verbose_stream() << "par2: worker " << id
                << " created (" << asms.size() << " assumptions)\n");
        }

        void run() {
            bool is_first_run = true;
            node_lease lease;
            expr_ref_vector cube(m);

            while (true) {
                if (!b.get_cube(m_g2l, id, cube, is_first_run, lease)) {
                    IF_VERBOSE(1, verbose_stream() << "par2 worker " << id
                        << ": no more cubes\n");
                    return;
                }
                is_first_run = false;

                collect_shared_clauses();

                lbool r = check_cube(cube);

                if (b.lease_canceled(lease)) {
                    IF_VERBOSE(1, verbose_stream() << "par2 worker " << id
                        << ": lease canceled\n");
                    lease = {};
                    m.limit().dec_cancel();
                    continue;
                }

                if (!m.inc()) return;

                switch (r) {

                case l_undef: {
                    update_max_conflicts();
                    IF_VERBOSE(1, verbose_stream() << "par2 worker " << id
                        << ": undef – attempting split\n");
                    expr_ref atom = get_split_atom(cube);
                    if (atom) {
                        b.try_split(m_l2g, id, lease, atom.get(),
                                    m_config.m_threads_max_conflicts);
                    }
                    else {
                        b.release_lease(id, lease);
                    }
                    if (m_config.m_share_units) share_units();
                    break;
                }

                case l_true: {
                    IF_VERBOSE(1, verbose_stream() << "par2 worker " << id
                        << ": SAT\n");
                    model_ref mdl;
                    s->get_model(mdl);
                    if (mdl)
                        b.set_sat(m_l2g, *mdl);
                    return;
                }

                case l_false: {
                    IF_VERBOSE(1, verbose_stream() << "par2 worker " << id
                        << ": UNSAT cube\n");
                    expr_ref_vector core(m);
                    s->get_unsat_core(core);

                    /* Filter to only cube literals (exclude base assumptions). */
                    expr_ref_vector cube_core(m);
                    for (expr* c : core) {
                        if (cube.contains(c))
                            cube_core.push_back(c);
                    }

                    /* If core contains none of the cube lits, the whole
                     * problem is UNSAT independent of the cube path. */
                    if (cube_core.empty()) {
                        b.set_unsat(m_l2g, core);
                        return;
                    }

                    b.backtrack(m_l2g, id, cube_core, lease);

                    if (m_config.m_share_conflicts) {
                        /* Share the negation of the cube-core conjunction
                         * as a learned clause: ¬(c₁ ∧ … ∧ cₙ) ≡ ¬c₁ ∨ … ∨ ¬cₙ */
                        expr_ref_vector neg_lits(m);
                        for (expr* c : cube_core)
                            neg_lits.push_back(mk_not(expr_ref(c, m)));
                        expr_ref clause(mk_or(neg_lits), m);
                        b.collect_clause(m_l2g, id, clause.get());
                    }
                    if (m_config.m_share_units) share_units();
                    break;
                }

                } // switch
            } // while
        } // run()

        void cancel() {
            m.limit().cancel();
        }

        void cancel_lease() {
            m.limit().inc_cancel();
        }

        void collect_statistics(statistics& st) const {
            s->collect_statistics(st);
        }

        reslimit& limit() { return m.limit(); }
    }; // class worker

    /* ---- members ---- */
    ref<solver>               m_solver;
    ast_manager&              m_manager;
    params_ref                m_params;
    scoped_ptr_vector<worker> m_workers;
    batch_manager             m_batch_manager;
    statistics                m_stats;

public:

    parallel_solver(solver* s, params_ref const& p)
        : m_solver(s),
          m_manager(s->get_manager()),
          m_params(p),
          m_batch_manager(s->get_manager(), *this) {}

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
        if (num_threads < 2) num_threads = 2;

        IF_VERBOSE(1, verbose_stream() << "par2: launching " << num_threads
            << " threads\n");

        if (m_manager.has_trace_stream())
            throw default_exception(
                "parallel_tactic2 does not work with trace streams");

        /* Build workers – each gets a translated solver copy. */
        m_workers.reset();
        scoped_limits sl(m_manager.limit());
        params_ref worker_params(m_params);
        worker_params.set_bool("override_incremental", true);

        for (unsigned i = 0; i < num_threads; ++i) {
            auto* w = alloc(worker, i, *this, *m_solver, worker_params, asms);
            m_workers.push_back(w);
            sl.push_child(&(w->limit()));
        }

        m_batch_manager.initialize(num_threads);

        /* Launch threads. */
        vector<std::thread> threads;
        for (auto* w : m_workers)
            threads.push_back(std::thread([w]() { w->run(); }));

        for (auto& t : threads)
            t.join();

        /* Collect per-worker statistics. */
        for (auto* w : m_workers)
            w->collect_statistics(m_stats);
        m_batch_manager.collect_statistics(m_stats);

        m_manager.limit().reset_cancel();

        lbool result = m_batch_manager.get_result();

        if (result == l_true)
            mdl = m_batch_manager.get_model();

        if (result == l_false) {
            for (expr* c : m_batch_manager.get_unsat_core())
                core.push_back(c);
        }

        m_workers.reset();
        return result;
    }

    void collect_statistics(statistics& st) const {
        st.copy(m_stats);
    }

    void reset_statistics() {
        m_stats.reset();
    }
}; // class parallel_solver

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
        extract_clauses_and_dependencies(g, clauses, assumptions_raw,
                                         bool2dep, fmc);
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
        case l_true:
            g->reset();
            if (g->models_enabled() && mdl) {
                if (fmc)
                    g->add(concat(fmc.get(), model2model_converter(mdl.get())));
                else
                    g->add(model2model_converter(mdl.get()));
            }
            break;

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

    void cleanup() override {
        m_stats.reset();
    }

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
}; // class parallel_tactic2

tactic* mk_parallel_tactic2(solver* s, params_ref const& p) {
    return alloc(parallel_tactic2, s, p);
}

#endif  /* !SINGLE_THREAD */
