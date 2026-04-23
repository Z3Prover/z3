/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_parallel.cpp

Abstract:

    Parallel SMT, portfolio loop specialized to SMT core.

Author:

    nbjorner 2020-01-31
    Ilana Shapiro 2025

--*/

#include "util/scoped_ptr_vector.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_translation.h"
#include "ast/simplifiers/then_simplifier.h"
#include "smt/smt_parallel.h"
#include "smt/smt_lookahead.h"
#include "solver/solver_preprocess.h"
#include "params/smt_parallel_params.hpp"

#include <cmath>
#include <mutex>
#include <condition_variable>

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

#ifdef SINGLE_THREAD

namespace smt {

    lbool parallel::operator()(expr_ref_vector const &asms) {
        return l_undef;
    }
}  // namespace smt

#else

#include <thread>

#define LOG_WORKER(lvl, s) IF_VERBOSE(lvl, verbose_stream() << "Worker " << id << s)
#define LOG_BB_WORKER(lvl, s) IF_VERBOSE(lvl, verbose_stream() << "Backbones Worker " << id << s)

namespace smt {

    static bool is_cancellation_exception(char const* msg) {
        return msg &&
            (strstr(msg, "canceled") != nullptr ||
             strstr(msg, "cancelled") != nullptr);
    }

    void parallel::sls_worker::run() {
        ptr_vector<expr> assertions;
        p.ctx.get_assertions(assertions);
        for (expr* e : assertions)
            m_sls->assert_expr(m_g2l(e));

        lbool res = l_undef;
        try {
            if (!m.inc())
                return;
            res = m_sls->check();
        } 
        catch (z3_exception& ex) {
            // Cancellation is normal in portfolio mode
            if (m.limit().is_canceled()) {
                IF_VERBOSE(1, verbose_stream() << "SLS worker canceled\n");
                return;
            }

            if (strstr(ex.what(), "unsupported for sls") != nullptr) {
                IF_VERBOSE(1, verbose_stream() << "SLS opted out: " << ex.what() << "\n");
                return;
            }

            // Anything else is a real error
            IF_VERBOSE(1, verbose_stream() << "SLS threw exception: " << ex.what() << "\n");
            b.set_exception(ex.what());
            return;
        }

        if (res == l_true) {         
            IF_VERBOSE(2, verbose_stream() << "SLS worker found SAT\n");
            model_ref mdl = m_sls->get_model();
            b.set_sat(m_l2g, *mdl);
        }
    }

    void parallel::backbones_worker::run() {
        bb_candidates bb_candidates;
        while (m.inc()) {
            if (!b.wait_for_backbone_job(id, m_g2l, bb_candidates, m.limit()))
                return;

            if (bb_candidates.empty())
                continue;

            LOG_BB_WORKER(1, " received batch of " << bb_candidates.size() << " candidates\n");
            
            unsigned local_cancel_epoch = b.get_cancel_epoch();
            auto canceled = [&] { return local_cancel_epoch != b.get_cancel_epoch(); };
            auto fallback_singletons = [&](expr_ref_vector const& chunk_lits, expr_ref_vector& bb_candidate_lits) {
                m_stats.m_fallback_singleton_checks++;
                for (expr* c : chunk_lits) {
                    if (!bb_candidate_lits.contains(c)) continue; // already handled in singleton core → backbone case below
                    
                    expr_ref bb_ref(c, m);
                    if (!m.inc() || canceled()) 
                        return;
                    
                    if (m_mode == bb_mode::bb_positive)
                        bb_ref = mk_not(bb_ref); // F ∧ U since check_backbone flips it back
                    
                    if (!b.is_global_backbone(m_l2g, bb_ref) && check_backbone(bb_ref)) {
                        m_stats.m_backbones_detected++;
                        LOG_BB_WORKER(1, " fallback found backbone: " << mk_bounded_pp(bb_ref.get(), m, 3) << "\n");
                        bool is_new_bb = b.collect_global_backbone(m_l2g, bb_ref);
                        if (is_new_bb) {
                            m_stats.m_backbones_found++;
                            ctx->assert_expr(bb_ref.get()); // since bb workers don't collect clauses they themselves shared
                        }
                    }
                    bb_candidate_lits.erase(c);
                }
            };
            
            m_stats.m_batches_total++;
            m_stats.m_candidates_total += bb_candidates.size();

            expr_ref_vector bb_candidate_lits(m);
            for (auto const& c : bb_candidates)
                bb_candidate_lits.push_back(c.lit);

            unsigned chunk_delta = 1;

            // in mode bb_neg this is Algorithm 7 from https://sat.inesc-id.pt/~mikolas/bb-aicom-preprint.pdf
            while (!bb_candidate_lits.empty() && !canceled() && m.inc()) {
                // remove candidates that the other backbone thread found to be backbones
                if (m_num_global_bb_threads > 1) {
                    for (unsigned i = 0; i < bb_candidate_lits.size();) {
                        expr* tmp = bb_candidate_lits.get(i);
                        if (b.is_global_backbone(m_l2g, tmp)) 
                            bb_candidate_lits.erase(i);                    
                        else
                            ++i;
                    }
                }

                unsigned chunk_size = std::min(m_bb_chunk_size * chunk_delta, bb_candidate_lits.size());
                expr_ref_vector chunk_lits(m);
                expr_ref_vector negated_chunk_lits(m);

                for (unsigned i = 0; i < chunk_size; ++i) {
                    expr *e = bb_candidate_lits.get(i);
                    chunk_lits.push_back(e);
                    negated_chunk_lits.push_back(m.mk_not(e));
                }

                expr_ref_vector bb_asms(m);
                if (m_mode == bb_mode::bb_negated)
                    bb_asms.append(negated_chunk_lits); // F ∧ ¬U
                else
                    bb_asms.append(chunk_lits); // F ∧ U

                collect_shared_clauses();

                while (true) {

                    if (!m.inc()) 
                        return;
                    if (canceled()) 
                        break;

                    m_stats.m_core_refinement_rounds++;

                    unsigned base_asms_sz = asms.size();
                    for (expr* a : bb_asms)
                        asms.push_back(a);

                    lbool r = l_undef;
                    try {
                        r = ctx->check(asms.size(), asms.data());
                    } catch (z3_error &err) {
                        if (!m.limit().is_canceled())
                            b.set_exception(err.error_code());
                    } catch (z3_exception &ex) {
                        if (!m.limit().is_canceled() && !is_cancellation_exception(ex.what()))
                            b.set_exception(ex.what());
                    } catch (...) {
                        if (!m.limit().is_canceled())
                            b.set_exception("unknown exception");
                    }
                    asms.shrink(base_asms_sz);

                    if (!m.inc()) 
                        return;
                    if (canceled()) 
                        break;

                    if (r == l_undef) {
                        LOG_BB_WORKER(1, " UNDEF at chunk_size=" << chunk_size << "\n");

                        if (chunk_size < bb_candidate_lits.size()) {
                            chunk_delta++; // try again with a bigger chunk
                            m_stats.m_num_chunk_increases++;
                            break;
                        }

                        LOG_BB_WORKER(1, " UNDEF and max chunk → fallback\n");

                        fallback_singletons(chunk_lits, bb_candidate_lits);
                        m_stats.m_fallback_reason_undef++;
                        chunk_delta = 1;
                        break;
                    }

                    if (r == l_true) {
                        LOG_BB_WORKER(1, " batch check returned SAT, thus entire formula is SAT\n");
                        model_ref mdl;
                        ctx->get_model(mdl);
                        b.set_sat(m_l2g, *mdl);
                        bb_candidates.reset();
                        return;
                    }

                    // ----- UNSAT: inspect core -----
                    expr_ref_vector bb_asms_in_core(m);
                    auto const& unsat_core = ctx->unsat_core();
                    
                    for (expr* a : unsat_core)
                        if (bb_asms.contains(a))
                            bb_asms_in_core.push_back(a);

                    // ---- empty core intersection → formula is UNSAT independent of backbone assumptions ----
                    if (bb_asms_in_core.empty()) {
                        expr_ref_vector core_vec(m);
                        for (expr* e : unsat_core)
                            core_vec.push_back(e);
                        b.set_unsat(m_l2g, core_vec);
                        return;
                    }

                    // ---- singleton core → backbone ----
                    if (bb_asms_in_core.size() == 1) {
                        expr* a = bb_asms_in_core.back();
                        expr_ref backbone_lit(m.mk_not(a), m);

                        m_stats.m_singleton_backbones++;
                        m_stats.m_backbones_detected++;

                        bool is_new_bb = b.collect_global_backbone(m_l2g, backbone_lit);

                        if (is_new_bb) {
                            m_stats.m_backbones_found++;
                            ctx->assert_expr(backbone_lit.get()); // since bb workers don't collect clauses they themselves shared
                        }

                        expr* candidate_to_remove =
                            (m_mode == bb_mode::bb_negated)
                            ? backbone_lit.get() // since core contains ¬candidates in negated mode
                            : a; // since core contains candidates in positive mode

                        bb_candidate_lits.erase(candidate_to_remove);
                    }

                    unsigned sz_before = bb_asms.size();
                    for (expr* a : bb_asms_in_core)
                        bb_asms.erase(a);
                    m_stats.m_lits_removed_by_core += sz_before - bb_asms.size();
                    chunk_delta = 1;

                    if (bb_asms.empty()) {
                        LOG_BB_WORKER(1, " no more negated chunk literals, fallback to individual checks\n");
                        fallback_singletons(chunk_lits, bb_candidate_lits);
                        m_stats.m_fallback_reason_chunk_exhausted++;
                        break;
                    }
                }
            }

            if (!canceled()) {
                b.cancel_current_backbone_batch();
            }
            bb_candidates.reset();
        }
    }

    void parallel::backbones_worker::cancel() {
        LOG_BB_WORKER(1, " BACKBONES WORKER cancelling\n");
        m.limit().cancel();
    }
    
    bool parallel::batch_manager::collect_global_backbone(ast_translation &l2g, expr_ref const &backbone) {
        IF_VERBOSE(1, verbose_stream() << "collect-global-backbone\n");
        std::scoped_lock lock(mux);
        SASSERT(&m == &l2g.to());
        
        if (is_global_backbone_unlocked(l2g, backbone))
            return false;
        
        expr_ref g_bb_ref(l2g(backbone.get()), m);
        m_global_backbones.push_back(g_bb_ref);
       
        IF_VERBOSE(1, verbose_stream() << " Found and sharing new global backbone: " << mk_bounded_pp(g_bb_ref, m, 3) << "\n");
        collect_clause_unlocked(l2g, /*source_worker_id=*/UINT_MAX, backbone.get());

        expr_ref neg_g_bb_ref(mk_not(g_bb_ref), m);
        vector<cube_config::literal> g_core;
        g_core.push_back(neg_g_bb_ref);
        vector<node_lease> targets;
        collect_matching_targets_unlocked(nullptr, neg_g_bb_ref, g_core, targets);
        if (!targets.empty()) {
            IF_VERBOSE(1, verbose_stream() << " Closing negation of the new global backbone: " << mk_bounded_pp(g_bb_ref, m, 3) << "\n");
            expr_ref_vector l_core(l2g.from());
            l_core.push_back(mk_not(backbone));
            backtrack_unlocked(l2g, UINT_MAX, l_core, nullptr, &targets);
        }

        return true;
    }

   void parallel::backbones_worker::collect_statistics(::statistics& st) const {
        st.update("bb-batches-total", m_stats.m_batches_total);
        st.update("bb-candidates-total", m_stats.m_candidates_total);
        st.update("bb-backbones-detected", m_stats.m_backbones_detected);
        st.update("bb-backbones-found", m_stats.m_backbones_found);
        st.update("bb-core-refinement-rounds", m_stats.m_core_refinement_rounds);
        st.update("bb-singleton-backbones", m_stats.m_singleton_backbones);
        st.update("bb-fallback-singleton-checks", m_stats.m_fallback_singleton_checks);
        st.update("bb-fallback-chunk-exhausted", m_stats.m_fallback_reason_chunk_exhausted);
        st.update("bb-fallback-undef", m_stats.m_fallback_reason_undef);
        st.update("bb-literals-removed-by-core", m_stats.m_lits_removed_by_core);
        st.update("bb-num-chunk-increases", m_stats.m_num_chunk_increases);

        double backbone_yield = 0.0;
        if (m_stats.m_candidates_total > 0)
            backbone_yield = 100.0 * (double)m_stats.m_backbones_found / (double)m_stats.m_candidates_total;
        double avg_backbones_per_batch = 0.0;
        if (m_stats.m_batches_total > 0)
            avg_backbones_per_batch = (double)m_stats.m_backbones_found / (double)m_stats.m_batches_total;
        double core_refinement_cost = 0.0;
        if (m_stats.m_batches_total > 0)
            core_refinement_cost = (double)m_stats.m_core_refinement_rounds / (double)m_stats.m_batches_total;
        double core_effectiveness = 0.0;
        if (m_stats.m_core_refinement_rounds > 0)
            core_effectiveness = (double)m_stats.m_lits_removed_by_core / (double)m_stats.m_core_refinement_rounds;

        st.update("bb-backbone-yield-pct", backbone_yield);
        st.update("bb-avg-backbones-per-batch", avg_backbones_per_batch);
        st.update("bb-core-refinement-rounds-per-batch", core_refinement_cost);
        st.update("bb-core-effectiveness-lit-removed-per-round", core_effectiveness);
    }

    void parallel::sls_worker::cancel() {
        IF_VERBOSE(1, verbose_stream() << " SLS WORKER cancelling\n");
        m.limit().cancel();
    }

    void parallel::sls_worker::collect_statistics(::statistics &st) const {
        m_sls->collect_statistics(st);
    }

    parallel::core_minimizer_worker::core_minimizer_worker(parallel& p, expr_ref_vector const& _asms)
        : b(p.m_batch_manager), asms(m), m_smt_params(p.ctx.get_fparams()), m_g2l(p.ctx.m, m), m_l2g(m, p.ctx.m) {
        for (expr* e : _asms)
            asms.push_back(m_g2l(e));
        IF_VERBOSE(1, verbose_stream() << "Initialized core minimizer thread\n");
        ctx = alloc(context, m, m_smt_params, p.ctx.get_params());
        ctx->set_logic(p.ctx.m_setup.get_logic());
        context::copy(p.ctx, *ctx, true);
        ctx->pop_to_base_lvl();
        ctx->get_fparams().m_preprocess = false;
    }

    void parallel::core_minimizer_worker::cancel() {
        IF_VERBOSE(1, verbose_stream() << "Core minimizer cancelling\n");
        m.limit().cancel();
    }

    void parallel::core_minimizer_worker::collect_statistics(::statistics& st) const {
        ctx->collect_statistics(st);
        st.update("parallel-core-minimize-calls", m_num_core_minimize_calls);
        st.update("parallel-core-minimize-undef", m_num_core_minimize_undef);
        st.update("parallel-core-minimize-refined", m_num_core_minimize_refined);
        st.update("parallel-core-minimize-lits-removed", m_num_core_minimize_lits_removed);
    }

    void parallel::core_minimizer_worker::minimize_unsat_core(expr_ref_vector& core) {
        expr_ref_vector original_core(m);
        expr_ref_vector unknown(m), mus(m), trial(m), core_exprs(m);
        unsigned original_size = core.size();
        ++m_num_core_minimize_calls;
        original_core.append(core);
        unknown.append(core);

        // Invariant: F and mus and unknown is UNSAT.
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
                flet<unsigned> _max_conflicts(ctx->get_fparams().m_max_conflicts, m_core_minimize_conflict_budget);
                r = ctx->check(trial.size(), trial.data());
            }
            catch (...) {
                r = l_undef;
            }

            switch (r) {
            case l_undef:
                ++m_num_core_minimize_undef;
                mus.push_back(lit);
                break;
            case l_true: {
                model_ref mdl;
                ctx->get_model(mdl);
                b.set_sat(m_l2g, *mdl);
                return;
            }
            case l_false:
                core_exprs.reset();
                core_exprs.append(ctx->unsat_core());
                SASSERT(core_exprs.contains(not_lit));
                if (core_exprs.contains(not_lit)) {
                    ++m_num_core_minimize_refined;
                    unknown.reset();
                    expr_ref_vector new_mus(m);
                    for (expr* c : core_exprs) {
                        if (mus.contains(c))
                            new_mus.push_back(c);
                        else
                            unknown.push_back(c);
                    }
                    mus.reset();
                    mus.append(new_mus);
                }
                break;
            default:
                UNREACHABLE();
                core.reset();
                core.append(original_core);
                return;
            }
        }

        SASSERT(unknown.empty()); // or, append unknown to core, to reflect loop invariant and in case you end up adding an early exit.
        core.reset();
        core.append(mus);
        if (core.size() < original_size)
            m_num_core_minimize_lits_removed += original_size - core.size();
        return;
    }

    void parallel::core_minimizer_worker::run() {
        while (m.inc()) {
            search_tree::node<cube_config>* source = nullptr;
            expr_ref_vector core(m);
            if (!b.wait_for_core_min_job(m_g2l, source, core, m.limit()))
                return;

            unsigned original_size = core.size();
            if (original_size <= 1)
                continue;

            collect_shared_clauses();

            expr_ref_vector minimized(m);
            minimized.append(core);
            minimize_unsat_core(minimized);

            if (minimized.size() < original_size)
                b.publish_minimized_core(m_l2g, source, original_size, minimized);
        }
    }

    void parallel::worker::prepare_backbone_candidates(u_map<double>& original_activities, phase_snapshots& original_phases) {
        bb_candidates local_candidates = find_backbone_candidates();
        b.collect_backbone_candidates(m_l2g, local_candidates);
        if (m_config.m_local_backbones) {
            LOG_WORKER(1, " LOCAL BACKBONE DETECTION\n");

            // Pull candidates from the global batch manager pool so that
            // backbone signals discovered by other workers inform this experiment.
            // Fall back to locally-derived candidates if the global pool is empty yet.
            bb_candidates bb_cands = b.return_global_bb_candidates(m_g2l);
            if (bb_cands.empty()) {
                LOG_WORKER(1, " no global bb candidates, using local bb candidates\n");
                bb_cands = local_candidates;
            }

            for (smt::parallel::bb_candidate const& bb : bb_cands) {
                // Set the phase of the candidates to the negation of their assumed values
                LOG_WORKER(2, " backbone candidate: " << mk_bounded_pp(bb.lit, m, 3) << "\n");

                expr* lit = bb.lit.get();
                expr* atom = lit;
                
                // checks whether lit is a negation: if yes, writes the inner expression into atom
                bool is_negated = m.is_not(lit, atom);

                // Candidates from other workers may not be internalized in this context.
                if (!ctx->b_internalized(atom))
                    continue;
                
                sat::bool_var v = ctx->get_bool_var(atom);
                if (v == sat::null_bool_var)
                    continue;

                bool phase = false;  // set to false if tuning for UNSAT, set to true if tuning for SAT
                if (is_negated)
                    phase = !phase;

                // auto const& d = ctx->get_bdata(v);
                // bool has_phase_snapshot = false;
                // for (auto const& snapshot : original_phases) {
                //     if (snapshot.v == v) {
                //         has_phase_snapshot = true;
                //         break;
                //     }
                // }
                // if (!has_phase_snapshot) {
                //     original_phases.push_back(phase_snapshot{v, d.m_phase_available, d.m_phase});
                // }

                ctx->force_phase(v, phase);
                LOG_WORKER(2, " backbone candidate forced phase: " << mk_bounded_pp(lit, m, 3) << " := " << (phase ? "true" : "false") << "\n");

                auto const& activities = ctx->get_activity_vector();
                double max_activity = 0.0;
                for (unsigned i = 0; i < activities.size(); ++i)
                    max_activity = std::max(max_activity, activities[i]);

                // double saved_activity = 0.0;
                // if (!original_activities.find(v, saved_activity))
                //     original_activities.insert(v, ctx->get_activity(v));

                // Promote this candidate above all others
                double eps = 1.0;
                ctx->set_activity(v, max_activity + eps);

                LOG_WORKER(2, " boosted activity of backbone candidate to " << (max_activity + eps) << "\n");
            }
        }
        if (!m.inc())
            return;
    }

    void parallel::worker::run() {
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

            u_map<double> original_activities;
            phase_snapshots original_phases;
            if (m_config.m_local_backbones || m_config.m_global_backbones) { 
                prepare_backbone_candidates(original_activities, original_phases);
            }
            

            lbool r = check_cube(cube);

            if (b.lease_canceled(lease)) {
                LOG_WORKER(1, " abandoning canceled lease\n");
                lease = {};
                m.limit().dec_cancel();
                continue;
            }

             if (!m.inc())
                return;

            // if (m_config.m_local_backbones) {
            //     // Restore activities of backbone candidates to old values after the search
            //     for (auto const& [v, act] : original_activities) {
            //         ctx->set_activity(v, act);
            //     }
            //     for (auto const& snapshot : original_phases) {
            //         ctx->unforce_phase(snapshot.v, snapshot.original_phase_available, snapshot.original_phase);
            //     }
            // }

            switch (r) {
            case l_undef: {
                update_max_thread_conflicts();
                LOG_WORKER(1, " found undef cube\n");
                if (m_config.m_max_cube_depth <= cube.size())
                    goto check_cube_start;

                auto atom = get_split_atom();
                if (!atom)
                    goto check_cube_start;
                b.try_split(m_l2g, id, lease, atom, m_config.m_threads_max_conflicts);
                lease = {};
                simplify();
                break;
            }
            case l_true: {
                LOG_WORKER(1, " found sat cube\n");
                model_ref mdl;
                ctx->get_model(mdl);
                b.set_sat(m_l2g, *mdl);
                return;
            }
            case l_false: {
                expr_ref_vector unsat_core(m);
                unsat_core.append(ctx->unsat_core());
                LOG_WORKER(2, " unsat core:\n";
                           for (auto c : unsat_core) verbose_stream() << mk_bounded_pp(c, m, 3) << "\n");
                // If the unsat core only contains external assumptions,
                // unsatisfiability does not depend on the current cube and the entire problem is unsat.
                if (all_of(unsat_core, [&](expr *e) { return asms.contains(e); })) {
                    LOG_WORKER(1, " determined formula unsat\n");
                    b.set_unsat(m_l2g, unsat_core);
                    return;
                }

                LOG_WORKER(1, " found unsat cube\n");
                node* source = lease.node;
                b.backtrack(m_l2g, id, unsat_core, lease);
                if (m_config.m_core_minimize)
                    b.enqueue_core_minimization(m_l2g, source, unsat_core);
                lease = {};

                if (m_config.m_share_conflicts)
                    b.collect_clause(m_l2g, id, mk_not(mk_and(unsat_core)));

                break;
            }
            }
            if (m_config.m_share_units)
                share_units();
        }
    }

    parallel::worker::worker(unsigned id, parallel &p, expr_ref_vector const &_asms)
        : id(id), p(p), b(p.m_batch_manager), asms(m), m_smt_params(p.ctx.get_fparams()), m_g2l(p.ctx.m, m),
          m_l2g(m, p.ctx.m) {
        for (auto e : _asms)
            asms.push_back(m_g2l(e));
        LOG_WORKER(1, " created with " << asms.size() << " assumptions\n");
        m_smt_params.m_random_seed += id;  // ensure different random seed for each worker
        ctx = alloc(context, m, m_smt_params, p.ctx.get_params());
        ctx->set_logic(p.ctx.m_setup.get_logic());
        context::copy(p.ctx, *ctx, true);
        // don't share initial units
        ctx->pop_to_base_lvl();
        m_num_shared_units = ctx->assigned_literals().size();
        m_num_initial_atoms = ctx->get_num_bool_vars();
        ctx->get_fparams().m_preprocess = false;  // avoid preprocessing lemmas that are exchanged

        smt_parallel_params pp(p.ctx.m_params);
        m_config.m_inprocessing = pp.inprocessing();
        m_config.m_global_backbones = pp.num_global_bb_threads() > 0;
        m_config.m_local_backbones = pp.local_backbones();
        m_config.m_core_minimize = pp.core_minimize();
    }

    parallel::sls_worker::sls_worker(parallel& p)
        : p(p), b(p.m_batch_manager), m(), m_g2l(p.ctx.m, m), m_l2g(m, p.ctx.m) {
        IF_VERBOSE(1, verbose_stream() << "Initialized SLS portfolio thread\n");
        m_params.append(p.ctx.m_params);
        m_sls = alloc(sls::smt_solver, m, m_params);
    }

    parallel::backbones_worker::backbones_worker(unsigned id, parallel &p, expr_ref_vector const &_asms)
        : id(id), b(p.m_batch_manager), m(), asms(m), m_smt_params(p.ctx.get_fparams()), m_g2l(p.ctx.m, m), m_l2g(m, p.ctx.m) {
        for (auto e : _asms)
            asms.push_back(m_g2l(e));
        IF_VERBOSE(1, verbose_stream() << "Initialized backbones thread " << id << "\n");
        m_mode = id == 0 ? bb_mode::bb_negated : bb_mode::bb_positive;
        ctx = alloc(context, m, m_smt_params, p.ctx.get_params());
        ctx->set_logic(p.ctx.m_setup.get_logic());
        ctx->get_fparams().m_max_conflicts = m_bb_conflicts_per_chunk;
        context::copy(p.ctx, *ctx, true);

        smt_parallel_params pp(p.ctx.m_params);
        m_num_global_bb_threads = pp.num_global_bb_threads();
    }

    parallel::bb_candidates parallel::worker::find_backbone_candidates(unsigned k) {
        bb_candidates backbone_candidates;
        expr_ref candidate(m);
        unsigned curr_time = ctx->m_stats.m_num_assignments;

        for (bool_var v = 0; v < ctx->get_num_bool_vars(); ++v) {
            if (ctx->get_assignment(v) != l_undef && ctx->get_assign_level(v) == ctx->m_base_lvl)
                continue;

            candidate = ctx->bool_var2expr(v);
            if (!candidate)
                continue;

            auto birth = ctx->m_birthdate[v];
            auto age = curr_time - birth;

            auto const& d = ctx->get_bdata(v);
            if (d.m_phase_available && !d.m_phase)
                candidate = m.mk_not(candidate);

            if (b.is_global_backbone(m_l2g, candidate))
                continue;

            bb_candidate bb_cand(m, candidate, age, 1);
            backbone_candidates.push_back(bb_cand);
        }
        
        // sort from oldest to youngest
        std::stable_sort(
            backbone_candidates.begin(), 
            backbone_candidates.end(), 
            [](bb_candidate const& a, bb_candidate const& b) {
                return a.age > b.age;
            }
        );

        // take top-k oldest 
        if (backbone_candidates.size() > k)
            backbone_candidates.shrink(k);
        
        return backbone_candidates;
    }

    // 
    // Assume the negation of all candidates (or a batch of them)
    // run the solver with a low budget of conflicts
    // if the unsat core contains a single candidate we have found a backbone literal
    // 
    bool parallel::backbones_worker::check_backbone(expr* bb_candidate) {
        unsigned sz = asms.size();
        asms.push_back(m.mk_not(bb_candidate));
        
        lbool r = l_undef;
        try {
            r = ctx->check(asms.size(), asms.data());
        } catch (z3_error &err) {
            if (!m.limit().is_canceled())
                b.set_exception(err.error_code());
        } catch (z3_exception &ex) {
            if (!m.limit().is_canceled() && !is_cancellation_exception(ex.what()))
                b.set_exception(ex.what());
        } catch (...) {
            if (!m.limit().is_canceled())
                b.set_exception("unknown exception");
        }

        asms.shrink(sz);

        LOG_BB_WORKER(1, " RESULT: " << r << " FOR CANDIDATE: " << mk_bounded_pp(bb_candidate, m, 3) << "\n");

        if (r == l_false) {
            auto core = ctx->unsat_core();
            if (core.size() == 1) {
                return true;
            }                
        }

        return false;
    }

    void parallel::worker::share_units() {
        // Collect new units learned locally by this worker and send to batch manager
        
        unsigned sz = ctx->assigned_literals().size();
        for (unsigned j = m_num_shared_units; j < sz; ++j) {  // iterate only over new literals since last sync
            literal lit = ctx->assigned_literals()[j];

            // filter by assign level: do not pop to base level as this destroys the current search state
            if (ctx->get_assign_level(lit) > ctx->m_base_lvl)
                continue;

            if (!ctx->is_relevant(lit.var()) && m_config.m_share_units_relevant_only)
                continue;

            if (m_config.m_share_units_initial_only && lit.var() >= m_num_initial_atoms) {
                LOG_WORKER(4, " Skipping non-initial unit: " << lit.var() << "\n");
                continue;  // skip non-initial atoms if configured to do so
            }

            expr_ref e(ctx->bool_var2expr(lit.var()), ctx->m);  // turn literal into a Boolean expression
            if (m.is_and(e) || m.is_or(e))
                continue;

            if (lit.sign())
                e = mk_not(e);  // negate if literal is negative
            b.collect_clause(m_l2g, id, e);
        }
        m_num_shared_units = sz;
    }

    void parallel::worker::simplify() {
        if (!m.inc())
            return;
        // first attempt: one-shot simplification of the context.
        // a precise schedule of repeated simplification is TBD.
        // also, the in-processing simplifier should be applied to
        // a current set of irredundant clauses that may be reduced by
        // unit propagation. By including the units we are effectively
        // repeating unit propagation, but potentially not subsumption or
        // Boolean simplifications that a solver could perform (smt_context doesnt really)
        // Integration of inprocssing simplifcation here or in sat/smt solver could
        // be based on taking the current clause set instead of the asserted formulas.
        if (!m_config.m_inprocessing)
            return;
        if (m_config.m_inprocessing_delay > 0) {
            --m_config.m_inprocessing_delay;
            return;
        }
        ctx->pop_to_base_lvl();
        if (ctx->m_base_lvl > 0)
            return;                       // simplification only at base level
        m_config.m_inprocessing = false;  // initial strategy is to immediately disable inprocessing for future calls.
        dependent_expr_simplifier *s = ctx->m_simplifier.get();
        if (!s) {
            // create a simplifier if none exists
            // initialize it to a default pre-processing simplifier.
            ctx->m_fmls = alloc(base_dependent_expr_state, m);
            auto then_s = alloc(then_simplifier, m, ctx->get_params(), *ctx->m_fmls);
            s = then_s;
            ctx->m_simplifier = s;
            init_preprocess(m, ctx->get_params(), *then_s, *ctx->m_fmls);
        }

        dependent_expr_state &fmls = *ctx->m_fmls.get();
        // extract assertions from ctx.
        // it is possible to track proof objects here if wanted.
        // feed them to the simplifier
        ptr_vector<expr> assertions;
        expr_ref_vector units(m);
        ctx->get_assertions(assertions);
        ctx->get_units(units);
        for (expr *e : assertions)
            fmls.add(dependent_expr(m, e, nullptr, nullptr));
        for (expr *e : units)
            fmls.add(dependent_expr(m, e, nullptr, nullptr));

        // run in-processing on the assertions
        s->reduce();

        scoped_ptr<context> new_ctx = alloc(context, m, m_smt_params, p.ctx.get_params());
        // extract simplified assertions from the simplifier
        // create a new context with the simplified assertions
        // update ctx with the new context.
        for (unsigned i = 0; i < fmls.qtail(); ++i) {
            auto const &de = fmls[i];
            new_ctx->assert_expr(de.fml());
        }

        asserted_formulas &src_af = ctx->m_asserted_formulas;
        asserted_formulas &dst_af = new_ctx->m_asserted_formulas;
        src_af.get_macro_manager().copy_to(dst_af.get_macro_manager());
        new_ctx->copy_user_propagator(*ctx, true);
        ctx = new_ctx.detach();
        ctx->setup_context(true);
        ctx->internalize_assertions();
        auto old_atoms = m_num_initial_atoms;
        m_num_shared_units = ctx->assigned_literals().size();
        m_num_initial_atoms = ctx->get_num_bool_vars();
        LOG_WORKER(1, " inprocess " << old_atoms << " -> " << m_num_initial_atoms << "\n");
    }

    void parallel::worker::collect_statistics(::statistics &st) const {
        ctx->collect_statistics(st);
        st.update("parallel-core-minimize-calls", m_num_core_minimize_calls);
        st.update("parallel-core-minimize-undef", m_num_core_minimize_undef);
        st.update("parallel-core-minimize-refined", m_num_core_minimize_refined);
        st.update("parallel-core-minimize-lits-removed", m_num_core_minimize_lits_removed);
    }

    void parallel::worker::cancel() {
        LOG_WORKER(1, " canceling\n");
        m.limit().cancel();
    }

    void parallel::worker::cancel_lease() {
        LOG_WORKER(1, " canceling lease\n");
        m.limit().inc_cancel();
    }

    void parallel::batch_manager::release_lease_unlocked(unsigned worker_id, node* n) {
        if (worker_id >= m_worker_leases.size())
            return;
        auto &lease = m_worker_leases[worker_id];
        if (!lease.node || lease.node != n)
            return;
        m_search_tree.dec_active_workers(lease.node);
        lease = {};
    }

    void parallel::batch_manager::cancel_closed_leases_unlocked(unsigned source_worker_id) {
        unsigned n = std::min(m_worker_leases.size(), p.m_workers.size());
        for (unsigned worker_id = 0; worker_id < n; ++worker_id) {
            if (worker_id == source_worker_id)
                continue;
            auto const& lease = m_worker_leases[worker_id];
            
            // only cancel workers that currently hold a lease, whose lease is canceled,
            // and haven't already been signaled (prevents multiple inc_cancel() for same lease)
            if (lease.node && !lease.cancel_signaled && m_search_tree.is_lease_canceled(lease.node, lease.cancel_epoch)) {
                p.m_workers[worker_id]->cancel_lease();
                m_worker_leases[worker_id].cancel_signaled = true;
            }
        }
    }

    void parallel::batch_manager::backtrack(ast_translation &l2g, unsigned worker_id, expr_ref_vector const &core,
                                            node_lease const &lease) {
        std::scoped_lock lock(mux);
        vector<cube_config::literal> g_core;
        for (auto c : core)
            g_core.push_back(expr_ref(l2g(c), m));

        vector<node_lease> targets;
        collect_matching_targets_unlocked(lease.node, lease.node->get_literal().get(), g_core, targets);
        backtrack_unlocked(l2g, worker_id, core, &lease, targets.empty() ? nullptr : &targets);
    }

    void parallel::batch_manager::enqueue_core_minimization(ast_translation& l2g, node* source,
                                                            expr_ref_vector const& core) {
        std::scoped_lock lock(mux);
        if (m_state != state::is_running || !p.m_core_minimizer_worker || !source || core.empty())
            return;
        if (core.size() <= 1) {
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

    bool parallel::batch_manager::wait_for_core_min_job(ast_translation& g2l, search_tree::node<cube_config>*& source,
                                                        expr_ref_vector& core, reslimit& lim) {
        std::unique_lock lock(mux);
        m_core_min_cv.wait(lock, [&]() {
            return lim.is_canceled() || m_state != state::is_running || !m_core_min_jobs.empty();
        });

        if (lim.is_canceled() || m_state != state::is_running)
            return false;

        core_min_job* job = m_core_min_jobs.detach_back();
        m_core_min_jobs.pop_back();
        SASSERT(job);
        source = job->source;
        core.reset();
        for (expr* c : job->core)
            core.push_back(g2l(c));
        dealloc(job);
        return source != nullptr;
    }

    void parallel::batch_manager::publish_minimized_core(ast_translation& l2g, search_tree::node<cube_config>* source,
                                                         unsigned original_core_size, expr_ref_vector const& minimized_core) {
        std::scoped_lock lock(mux);
        if (m_state != state::is_running || !source || minimized_core.size() >= original_core_size) {
            ++m_stats.m_core_min_jobs_skipped;
            return;
        }

        vector<cube_config::literal> g_core;
        for (expr* c : minimized_core)
            g_core.push_back(expr_ref(l2g(c), m));

        // don't publish a minimized core if the node already has an equal-or-smaller core by the time the minimizer thread finishes 
        // (e.g. from another thread or from backtracking resulotion propagation)
        if (source->get_core().size() <= g_core.size()) {
            ++m_stats.m_core_min_jobs_skipped;
            return;
        }

        IF_VERBOSE(1, verbose_stream() << "Batch manager publishing minimized core "
                                       << original_core_size << " -> " << g_core.size() << "\n");

        m_search_tree.backtrack(source, g_core);

        vector<node_lease> targets;
        if (!g_core.empty()) {
            collect_matching_targets_unlocked(source, g_core[0].get(), g_core, targets);
            for (auto const& target : targets) {
                if (!m_search_tree.is_lease_canceled(target.node, target.cancel_epoch))
                    m_search_tree.backtrack(target.node, g_core);
            }
        }

        ++m_stats.m_core_min_jobs_published;
        cancel_closed_leases_unlocked(UINT_MAX);

        IF_VERBOSE(2, m_search_tree.display(verbose_stream() << bounded_pp_exprs(minimized_core) << "\n"););
        if (m_search_tree.is_closed()) {
            IF_VERBOSE(1, verbose_stream() << "Search tree closed by minimized core, setting UNSAT\n");
            m_state = state::is_unsat;
            SASSERT(p.ctx.m_unsat_core.empty());
            for (auto e : m_search_tree.get_core_from_root())
                p.ctx.m_unsat_core.push_back(e);
            cancel_background_threads();
        }
    }

    void parallel::batch_manager::collect_matching_targets_unlocked(node* source, expr* lit, vector<cube_config::literal> const& core,
                                                                    vector<node_lease>& targets) {
        targets.reset();
        if (!lit)
            return;

        auto is_ancestor_of = [&](node* ancestor, node* cur) {
            if (!ancestor)
                return false;
            for (node* p = cur; p; p = p->parent()) {
                if (p == ancestor)
                    return true;
            }
            return false;
        };

        auto path_contains = [&](node* cur, cube_config::literal const& lit) {
            for (node* p = cur; p; p = p->parent()) {
                if (p->get_literal() == lit)
                    return true;
            }
            return false;
        };

        auto path_contains_core = [&](node* cur) {
            return all_of(core, [&](cube_config::literal const& c) {
                return path_contains(cur, c);
            });
        };

        ptr_vector<node> matches;
        m_search_tree.find_nonclosed_nodes_with_literal(expr_ref(lit, m), matches);
        for (node* t : matches) {
            if (!t || t == source)
                continue;
            if (m_search_tree.is_lease_canceled(t, t->get_cancel_epoch()))
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
            for (node* p = t->parent(); p; p = p->parent()) {
                if (any_of(targets, [&](node_lease const& target) { return target.node == p; })) {
                    is_highest_ancestor = false;
                    break;
                }
            }
            if (!is_highest_ancestor)
                continue;

            targets.push_back({ t, t->get_cancel_epoch() });
        }
    }

    void parallel::batch_manager::backtrack_unlocked(ast_translation& l2g, unsigned worker_id, expr_ref_vector const& core,
                                                     node_lease const* lease, vector<node_lease> const* targets) {
        if (m_state != state::is_running)
            return;

        vector<cube_config::literal> g_core;
        for (auto c : core)
            g_core.push_back(expr_ref(l2g(c), m));

        SASSERT(lease != nullptr || targets != nullptr);
        bool has_open_targets = false;

        if (lease) {
            // we close/backtrack regardless of whether this lease is stale or not, as long as the lease isn't canceled
            // i.e. worker 1 splits this node, but then worker 2 determines UNSAT --> worker 2 is stale but we still close this node and backtrack
            if (m_search_tree.is_lease_canceled(lease->node, lease->cancel_epoch))
                return;
            has_open_targets = true;
            IF_VERBOSE(1, verbose_stream() << "Batch manager backtracking.\n");
            release_lease_unlocked(worker_id, lease->node);
            m_search_tree.backtrack(lease->node, g_core);
        }
        if (targets) {
            for (auto const& target : *targets) {
                if (m_search_tree.is_lease_canceled(target.node, target.cancel_epoch))
                    continue;

                has_open_targets = true;
                IF_VERBOSE(1, verbose_stream() << "Batch manager backtracking external targets.\n");
                m_search_tree.backtrack(target.node, g_core);
            }
        }
        if (!has_open_targets)
            return;

        // terminate on-demand the workers that are currently exploring the now-closed nodes
        cancel_closed_leases_unlocked(worker_id);

        IF_VERBOSE(2, m_search_tree.display(verbose_stream() << bounded_pp_exprs(core) << "\n"););
        if (m_search_tree.is_closed()) {
            IF_VERBOSE(1, verbose_stream() << "Search tree closed, setting UNSAT\n");
            m_state = state::is_unsat;
            SASSERT(p.ctx.m_unsat_core.empty());
            for (auto e : m_search_tree.get_core_from_root())
               p.ctx.m_unsat_core.push_back(e);
            cancel_background_threads();
        }
    }

    void parallel::batch_manager::try_split(ast_translation &l2g, unsigned worker_id,
                                        node_lease const &lease, expr *atom, unsigned effort) {
        std::scoped_lock lock(mux);
        
        if (m_state != state::is_running)
            return;

        if (m_search_tree.is_lease_canceled(lease.node, lease.cancel_epoch))
            return;

        expr_ref lit(m), nlit(m);
        lit = l2g(atom);
        nlit = mk_not(m, lit);
        bool did_split = m_search_tree.try_split(lease.node, lease.cancel_epoch, lit, nlit, effort);

        release_lease_unlocked(worker_id, lease.node);

        if (did_split) {
            ++m_stats.m_num_cubes;
            m_stats.m_max_cube_depth = std::max(m_stats.m_max_cube_depth, lease.node->depth() + 1);
            IF_VERBOSE(1, verbose_stream() << "Batch manager splitting on literal: " << mk_bounded_pp(lit, m, 3) << "\n");
        }
    }

    void parallel::batch_manager::release_lease(unsigned worker_id, node_lease const &lease) {
        std::scoped_lock lock(mux);
        release_lease_unlocked(worker_id, lease.node);
    }

    bool parallel::batch_manager::lease_canceled(node_lease const &lease) {
        std::scoped_lock lock(mux);
        return m_state == state::is_running && m_search_tree.is_lease_canceled(lease.node, lease.cancel_epoch);
    }

    void parallel::batch_manager::collect_clause(ast_translation &l2g, unsigned source_worker_id, expr *clause) {
        std::scoped_lock lock(mux);
        collect_clause_unlocked(l2g, source_worker_id, clause);
    }

    void parallel::batch_manager::collect_clause_unlocked(ast_translation &l2g, unsigned source_worker_id, expr *clause) {
        expr *g_clause = l2g(clause);
        if (!shared_clause_set.contains(g_clause)) {
            shared_clause_set.insert(g_clause);
            shared_clause sc{source_worker_id, expr_ref(g_clause, m)};
            shared_clause_trail.push_back(sc);
        }
    }

    void parallel::worker::collect_shared_clauses() {
        expr_ref_vector new_clauses = b.return_shared_clauses(m_g2l, m_shared_clause_limit, id);
        // iterate over new clauses and assert them in the local context
        for (expr *e : new_clauses) {
            ctx->assert_expr(e);
            LOG_WORKER(4, " asserting shared clause: " << mk_bounded_pp(e, m, 3) << "\n");
        }
    }

    void parallel::backbones_worker::collect_shared_clauses() {
        expr_ref_vector new_clauses = b.return_shared_clauses(m_g2l, m_shared_clause_limit, UINT_MAX);
        // iterate over new clauses and assert them in the local context
        for (expr *e : new_clauses) {
            ctx->assert_expr(e);
            LOG_BB_WORKER(4, " asserting shared clause: " << mk_bounded_pp(e, m, 3) << "\n");
        }
    }

    void parallel::core_minimizer_worker::collect_shared_clauses() {
        expr_ref_vector new_clauses = b.return_shared_clauses(m_g2l, m_shared_clause_limit, UINT_MAX);
        // iterate over new clauses and assert them in the local context
        for (expr *e : new_clauses) {
            ctx->assert_expr(e);
            IF_VERBOSE(4, verbose_stream() << "Core minimizer asserting shared clause: "
                                           << mk_bounded_pp(e, m, 3) << "\n";);
        }
    }

    void parallel::batch_manager::collect_backbone_candidates(ast_translation& l2g, bb_candidates& bb_candidates) {
        std::scoped_lock lock(mux);

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
            if (is_global_backbone_unlocked(l2g, c.lit))
                continue;

            expr* worker_lit = c.lit.get();
            expr_ref g_lit(l2g(worker_lit), m);
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
                continue;
            }

            // Find worst candidate to evict
            unsigned worst_idx = 0;
            double worst_rank = rank_of(m_bb_candidates[0]);

            for (unsigned i = 1; i < m_bb_candidates.size(); ++i) {
                double r = rank_of(m_bb_candidates[i]);
                if (r < worst_rank) {
                    worst_rank = r;
                    worst_idx = i;
                }
            }

            bb_candidate new_bb_candidate = bb_candidate(m, g_lit.get(), age, 1);
            if (rank_of(new_bb_candidate) > worst_rank)
                m_bb_candidates[worst_idx] = new_bb_candidate;
        }

        if (!m_bb_candidates.empty()) {
            std::stable_sort(
                m_bb_candidates.begin(),
                m_bb_candidates.end(),
                [&](bb_candidate const& a, bb_candidate const& b) {
                    return rank_of(a) > rank_of(b);
                }
            );
            m_bb_cv.notify_all();
        }
    }

    parallel::bb_candidates parallel::batch_manager::return_global_bb_candidates(ast_translation& g2l) {
        bb_candidates bb_candidates_local;
        std::scoped_lock lock(mux);
        for (auto const& gc : m_bb_candidates) {
            expr_ref l_lit(g2l(gc.lit.get()), g2l.to());
            bb_candidates_local.push_back(bb_candidate(g2l.to(), l_lit, gc.age, gc.hits));
        }
        return bb_candidates_local;
    }

    bool parallel::batch_manager::wait_for_backbone_job(unsigned bb_thread_id, ast_translation& g2l, bb_candidates& out, reslimit& lim) {
        out.reset();
        std::unique_lock<std::mutex> lock(mux);

        // ---- WAIT UNTIL:
        // (a) a new batch is ready that this thread hasn't seen yet, OR
        // (b) candidates are available AND the previous batch is finished (not in progress)
        m_bb_cv.wait(lock, [&]() {
            return lim.is_canceled() ||
                m_state != state::is_running ||
                m_bb_last_batch_processed[bb_thread_id] < m_bb_batch_id ||
                !m_bb_candidates.empty();
        });

        if (lim.is_canceled())
            return false;

        if (m_state != state::is_running)
            return false;

        // ---- NEED NEW BATCH? ----
        // Only create a new batch if this thread has already seen the current batch.
        if (m_bb_last_batch_processed[bb_thread_id] == m_bb_batch_id) {

            // pop new batch once
            unsigned n = std::min<unsigned>(m_bb_batch_size, m_bb_candidates.size());

            m_bb_current_batch.reset();
            for (unsigned i = 0; i < n; ++i) {
                m_bb_current_batch.push_back(m_bb_candidates.back());
                m_bb_candidates.pop_back();
            }

            m_bb_batch_id++;

            // wake all threads to see new batch
            m_bb_cv.notify_all();
        }

        for (auto const& gc : m_bb_current_batch) {
            expr_ref l_lit(g2l(gc.lit.get()), g2l.to());
            out.push_back(bb_candidate(g2l.to(), l_lit, gc.age, gc.hits));
        }

        m_bb_last_batch_processed[bb_thread_id] = m_bb_batch_id;
        return true;
    }

    expr_ref_vector parallel::batch_manager::return_shared_clauses(ast_translation &g2l, unsigned &worker_limit,
                                                                   unsigned worker_id) {
        std::scoped_lock lock(mux);
        expr_ref_vector result(g2l.to());
        for (unsigned i = worker_limit; i < shared_clause_trail.size(); ++i) {
            if (shared_clause_trail[i].source_worker_id != worker_id)
                result.push_back(g2l(shared_clause_trail[i].clause.get()));
        }
        worker_limit = shared_clause_trail.size();  // update the worker limit to the end of the current trail
        return result;
    }

    lbool parallel::worker::check_cube(expr_ref_vector const &cube) {
        for (auto &atom : cube)
            asms.push_back(atom);
        lbool r = l_undef;

        ctx->get_fparams().m_max_conflicts = std::min(m_config.m_threads_max_conflicts, m_config.m_max_conflicts);
        IF_VERBOSE(1, verbose_stream() << " Checking cube\n"
                                       << bounded_pp_exprs(cube)
                                       << "with max_conflicts: " << ctx->get_fparams().m_max_conflicts << "\n";);
        try {
            r = ctx->check(asms.size(), asms.data());
        } catch (z3_error &err) {
            if (!is_cancellation_exception(err.what()))
                b.set_exception(err.error_code());
        } catch (z3_exception &ex) {
            if (!is_cancellation_exception(ex.what()))
                b.set_exception(ex.what());
        } catch (...) {
            b.set_exception("unknown exception");
        }
        asms.shrink(asms.size() - cube.size());
        LOG_WORKER(1, " DONE checking cube " << r << "\n";);
        return r;
    }

    expr_ref parallel::worker::get_split_atom() {
        expr_ref result(m);
        double score = 0;
        unsigned n = 0;
        ctx->pop_to_search_lvl();
        for (bool_var v = 0; v < ctx->get_num_bool_vars(); ++v) {
            if (ctx->get_assignment(v) != l_undef)
                continue;
            expr *e = ctx->bool_var2expr(v);
            if (!e)
                continue;

            // don't split on a backbone
            if (m_config.m_global_backbones) {
                expr_ref e_ref(e, m);
                expr_ref neg_e_ref(mk_not(e_ref), m);
                if (b.is_global_backbone(m_l2g, e_ref) || b.is_global_backbone(m_l2g, neg_e_ref))
                    continue;
            }

            // Lightweight Proof Skeleton Approach
            // double new_score = ctx->m_lit_scores[0][v] * ctx->m_lit_scores[1][v];

            // ctx->m_lit_scores[0][v] /= 2;
            // ctx->m_lit_scores[1][v] /= 2;

            // VSIDS Approach
            double new_score = ctx->get_activity(v); 

            if (new_score > score || !result || (new_score == score && m_rand(++n) == 0)) {
                score = new_score;
                result = e;
            }
        }
        return result;
    }

    void parallel::batch_manager::set_sat(ast_translation &l2g, model &m) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager setting SAT.\n");
        if (m_state != state::is_running)
            return;
        m_state = state::is_sat;
        p.ctx.set_model(m.translate(l2g));
        cancel_background_threads();
    }

    void parallel::batch_manager::set_unsat(ast_translation &l2g, expr_ref_vector const &unsat_core) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager setting UNSAT.\n");
        if (m_state != state::is_running)
            return;
        m_state = state::is_unsat;

        // each call to check_sat needs to have a fresh unsat core
        SASSERT(p.ctx.m_unsat_core.empty());
        for (expr *e : unsat_core)
            p.ctx.m_unsat_core.push_back(l2g(e));
        cancel_background_threads();
    }

    void parallel::batch_manager::set_exception(unsigned error_code) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager setting exception code: " << error_code << ".\n");
        if (m_state != state::is_running)
            return;
        m_state = state::is_exception_code;
        m_exception_code = error_code;
        cancel_background_threads();
    }

    void parallel::batch_manager::set_exception(std::string const &msg) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager setting exception msg: " << msg << ".\n");
        if (m_state != state::is_running)
            return;
        m_state = state::is_exception_msg;
        m_exception_msg = msg;
        cancel_background_threads();
    }

    lbool parallel::batch_manager::get_result() const {
        if (m.limit().is_canceled())
            return l_undef;  // the main context was cancelled, so we return undef.
        switch (m_state) {
        case state::is_running:  // batch manager is still running, but all threads have processed their cubes, which
                                 // means all cubes were unsat
            throw default_exception("inconsistent end state");
        case state::is_unsat:
            return l_false;
        case state::is_sat:
            return l_true;
        case state::is_exception_msg:
            throw default_exception(m_exception_msg.c_str());
        case state::is_exception_code:
            throw z3_error(m_exception_code);
        default:
            UNREACHABLE();
            return l_undef;
        }
    }

    bool parallel::batch_manager::get_cube(ast_translation &g2l, unsigned id, expr_ref_vector &cube, bool is_first_run, node_lease &lease) {
        std::scoped_lock lock(mux);
        cube.reset();
        
        if (m_search_tree.is_closed()) {
            IF_VERBOSE(1, verbose_stream() << "all done\n";);
            return false;
        }
        if (m_state != state::is_running) {
            IF_VERBOSE(1, verbose_stream() << "aborting get_cube\n";);
            return false;
        }
        
        node *t = is_first_run ? m_search_tree.activate_root() : m_search_tree.activate_best_node();
        
        if (!t)
            return false;
        
        IF_VERBOSE(2, m_search_tree.display(verbose_stream()); verbose_stream() << "\n";);
        
        lease.node = t;
        lease.cancel_epoch = t->get_cancel_epoch();
        if (id >= m_worker_leases.size())
            m_worker_leases.resize(id + 1);
        m_worker_leases[id] = lease;
        
        while (t) {
            if (cube_config::literal_is_null(t->get_literal()))
                break;
            expr_ref lit(g2l.to());
            lit = g2l(t->get_literal().get());
            cube.push_back(std::move(lit));
            t = t->parent();
        }
        
        return true;
    }

    void parallel::batch_manager::initialize(unsigned num_global_bb_threads, unsigned initial_max_thread_conflicts) {
        m_state = state::is_running;

        m_num_global_bb_threads = num_global_bb_threads;
        m_bb_last_batch_processed.reset();
        m_bb_last_batch_processed.resize(m_num_global_bb_threads);
        m_bb_candidates.reset();
        m_core_min_jobs.reset();

        m_search_tree.reset();
        m_search_tree.set_effort_unit(initial_max_thread_conflicts);
        
        m_worker_leases.reset();
        m_worker_leases.resize(p.m_workers.size());
    }

    void parallel::batch_manager::collect_statistics(::statistics &st) const {
        st.update("parallel-num_cubes", m_stats.m_num_cubes);
        st.update("parallel-max-cube-size", m_stats.m_max_cube_depth);
        st.update("parallel-core-min-jobs-enqueued", m_stats.m_core_min_jobs_enqueued);
        st.update("parallel-core-min-jobs-published", m_stats.m_core_min_jobs_published);
        st.update("parallel-core-min-jobs-skipped", m_stats.m_core_min_jobs_skipped);
    }

    lbool parallel::operator()(expr_ref_vector const &asms) {
        smt_parallel_params pp(ctx.m_params);
        unsigned num_workers = std::min((unsigned)std::thread::hardware_concurrency(), ctx.get_fparams().m_threads);
        unsigned num_sls_threads = (pp.sls() ? 1 : 0);
        unsigned num_core_min_threads = (pp.core_minimize() ? 1 : 0);
        unsigned num_global_bb_threads = pp.num_global_bb_threads();          
        unsigned total_threads = num_workers + num_sls_threads + num_core_min_threads + num_global_bb_threads;

        IF_VERBOSE(1, verbose_stream() << "Parallel SMT with " << total_threads << " threads\n";);
        ast_manager &m = ctx.m;

        if (m.has_trace_stream())
            throw default_exception("trace streams have to be off in parallel mode");

        struct scoped_clear {
            parallel &p;
            scoped_clear(parallel &p) : p(p) {}
            ~scoped_clear() {
                p.m_workers.reset();
                p.m_sls_worker = nullptr;
                p.m_core_minimizer_worker = nullptr;
                p.m_global_backbones_workers.reset();
            }
        };
        scoped_clear clear(*this);

        m_workers.reset();
        m_core_minimizer_worker = nullptr;
        
        scoped_limits sl(m.limit());
        flet<unsigned> _nt(ctx.m_fparams.m_threads, 1);
        SASSERT(num_workers > 1);
        for (unsigned i = 0; i < num_workers; ++i)
            m_workers.push_back(alloc(worker, i, *this, asms));
        for (auto w : m_workers)
            sl.push_child(&(w->limit()));

        if (num_sls_threads == 1) {
            m_sls_worker = alloc(sls_worker, *this);
            sl.push_child(&(m_sls_worker->limit()));
        }
        if (pp.core_minimize()) {
            m_core_minimizer_worker = alloc(core_minimizer_worker, *this, asms);
            sl.push_child(&(m_core_minimizer_worker->limit()));
        }
        for (unsigned i = 0; i < num_global_bb_threads; ++i) {
            auto *w = alloc(backbones_worker, i, *this, asms);
            m_global_backbones_workers.push_back(w);
            sl.push_child(&(w->limit()));
        }
        IF_VERBOSE(1, verbose_stream() << "Launched " << m_workers.size() << " CDCL threads, "
                                       << (m_sls_worker ? 1 : 0) << " SLS threads, "
                                       << (m_core_minimizer_worker ? 1 : 0) << " core minimizer threads, "
                                       << m_global_backbones_workers.size() << " global backbone threads.\n";);

        m_batch_manager.initialize(num_global_bb_threads);
        
        // Launch threads
        vector<std::thread> threads;
        threads.resize(total_threads);
        unsigned thread_idx = 0;
        for (auto* w : m_workers) 
            threads[thread_idx++] = std::thread([&, w]() { w->run(); });                
        if (m_sls_worker)
            threads[thread_idx++] = std::thread([&]() { m_sls_worker->run(); });
        if (m_core_minimizer_worker)
            threads[thread_idx++] = std::thread([&]() { m_core_minimizer_worker->run(); });
        for (auto* w : m_global_backbones_workers) 
            threads[thread_idx++] = std::thread([&, w]() { w->run(); });                   


        // Wait for all threads to finish
        for (auto &th : threads)
            th.join();

        for (auto w : m_workers)
            w->collect_statistics(ctx.m_aux_stats);
        m_batch_manager.collect_statistics(ctx.m_aux_stats);
        if (m_sls_worker)
            m_sls_worker->collect_statistics(ctx.m_aux_stats);
        if (m_core_minimizer_worker)
            m_core_minimizer_worker->collect_statistics(ctx.m_aux_stats);
        for (auto* bb_w : m_global_backbones_workers)
            bb_w->collect_statistics(ctx.m_aux_stats);

        return m_batch_manager.get_result();
    }

}  // namespace smt
#endif
