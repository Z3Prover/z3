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

namespace smt {

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
        svector<bb_candidate> bb_candidates;

        while (m.inc()) {
            if (!b.wait_for_backbone_job(m_g2l, bb_candidates, m.limit()))
                return;

            if (bb_candidates.empty())
                continue;

            // Γ = candidates
            expr_ref_vector gamma(m);
            for (auto const& c : bb_candidates)
                gamma.push_back(c.lit);

            // ω = negated assumptions
            expr_ref_vector omega(m);
            for (expr* e : gamma)
                omega.push_back(m.mk_not(e));

            unsigned base_sz = asms.size();

            while (!gamma.empty()) {

                // push ω
                for (expr* a : omega)
                    asms.push_back(a);

                ctx->get_fparams().m_max_conflicts = 1000;

                lbool r = l_undef;
                try {
                    r = ctx->check(asms.size(), asms.data());
                } catch (...) {
                    asms.shrink(base_sz);
                    throw;
                }

                asms.shrink(base_sz);

                if (r == l_true) {
                    expr_ref_vector new_gamma(m);

                    for (expr* e : gamma) {
                        sat::bool_var v = ctx->get_bool_var(e);

                        if (v == sat::null_bool_var)
                            continue;

                        lbool val = ctx->get_assignment(v);

                        if (val == l_true) {
                            // still could be backbone
                            new_gamma.push_back(e);
                        }
                        // if false → cannot be backbone
                    }

                    gamma.reset();
                    gamma.append(new_gamma);

                    break;
                }
                // UNSAT → inspect core
                expr_ref_vector core = ctx->unsat_core();

                expr_ref_vector core_in_omega(m);
                for (expr* a : core)
                    if (omega.contains(a))
                        core_in_omega.push_back(a);

                if (core_in_omega.size() == 1) {
                    // singleton core → backbone found
                    expr* a = core_in_omega[0].get();
                    expr* bb = mk_not(m, a);

                    expr_ref bb_ref(bb, m);

                    IF_VERBOSE(1, verbose_stream()
                        << "Algorithm7 backbone: "
                        << mk_bounded_pp(bb_ref, m, 3) << "\n");

                    b.collect_global_backbone(m_l2g, bb_ref);

                    // remove from gamma
                    gamma.erase(bb);

                    // remove from omega
                    omega.erase(a);

                    continue;
                }

                // shrink ω
                for (expr* a : core_in_omega)
                    omega.erase(a);

                if (omega.empty()) {
                    // fallback → individual checks
                    for (expr* e : gamma) {
                        expr_ref bb_ref(e, m);
                        if (check_backbone(bb_ref))
                            b.collect_global_backbone(m_l2g, bb_ref);
                    }
                    break;
                }
            }

            bb_candidates.reset();
        }
    }


    void parallel::backbones_worker::cancel() {
        IF_VERBOSE(1, verbose_stream() << " BACKBONES WORKER cancelling\n");
        m.limit().cancel();
    }
    
    void parallel::batch_manager::collect_global_backbone(ast_translation& l2g, expr_ref const& backbone) {
        expr_ref g_bb(m);
        bool is_new_bb = false;

        {
            std::scoped_lock lock(mux);

            expr* local_e = l2g(backbone.get());

            if (!is_global_backbone(local_e)) {
                IF_VERBOSE(1, verbose_stream() << " Found new global backbone: " << mk_bounded_pp(local_e, m, 3) << "\n");

                m_global_backbones.push_back(local_e);

                g_bb = expr_ref(local_e, m);
                is_new_bb = true;
            }
        }

        if (!is_new_bb)
            return;

        IF_VERBOSE(1, verbose_stream() << " Sharing new global backbone: " << mk_bounded_pp(g_bb, m, 3) << "\n");
        collect_clause(l2g, /*source_worker_id=*/UINT_MAX, g_bb.get());

        node* t = nullptr;

        {
            std::scoped_lock lock(mux);
            expr_ref neg_bb(mk_not(m, g_bb.get()), m);
            t = m_search_tree.find_node_with_literal(neg_bb);
        }

        if (t) {
            IF_VERBOSE(1, verbose_stream() << " Backtracking on new global backbone: " << mk_bounded_pp(g_bb, m, 3) << "\n");
            expr_ref_vector core(m);
            core.push_back(g_bb);
            backtrack(l2g, core, t);
        }
    }

    void parallel::backbones_worker::collect_statistics(::statistics& st) const {
        st.update("bb-batch-total", m_batch_total);
        st.update("bb-num-total-batches", m_num_total_batches);
        st.update("bb-num-viable-batches", m_num_viable_batches);
        st.update("bb-candidates-tested", m_candidates_tested);
        st.update("bb-confirmed", m_candidates_confirmed);

        double batch_pct = 0.0;
        if (m_batch_total > 0)
            batch_pct = 100.0 * (double)m_candidates_tested / (double)m_batch_total;

        double confirm_pct = 0.0;
        if (m_candidates_tested > 0)
            confirm_pct = 100.0 * (double)m_candidates_confirmed / (double)m_candidates_tested;

        st.update("bb-batch-filter-pct", batch_pct);
        st.update("bb-success-rate-pct", confirm_pct);
    }

    void parallel::sls_worker::cancel() {
        IF_VERBOSE(1, verbose_stream() << " SLS WORKER cancelling\n");
        m.limit().cancel();
    }

    void parallel::sls_worker::collect_statistics(::statistics &st) const {
        m_sls->collect_statistics(st);
    }

    void parallel::worker::run() {
        search_tree::node<cube_config> *node = nullptr;
        expr_ref_vector cube(m);
        while (true) {

            if (!b.get_cube(m_g2l, id, cube, node)) {
                LOG_WORKER(1, " no more cubes\n");
                return;
            }
            collect_shared_clauses();

        check_cube_start:
            LOG_WORKER(1, " CUBE SIZE IN MAIN LOOP: " << cube.size() << "\n");

            u_map<double> original_activities;
            if (m_config.m_local_backbones) {
                LOG_WORKER(1, " BACKBONE DETECTION\n");
                svector<smt::parallel::bb_candidate> backbone_candidates = find_backbone_candidates();
                for (smt::parallel::bb_candidate const& bb : backbone_candidates) {
                    // Set the phase of the candidates to the negation of their assumed values
                    LOG_WORKER(2, " backbone candidate: " << mk_bounded_pp(bb.lit, m, 3) << "\n");
                    expr* atom = bb.lit.get();
                    bool phase = false;

                    if (m.is_not(atom)) {
                        phase = true;
                        atom = to_app(atom)->get_arg(0);
                    }

                    sat::bool_var v = ctx->get_bool_var(atom);
                    ctx->force_phase(v, phase);
                    LOG_WORKER(2, " backbone candidate forced phase: " << mk_bounded_pp(atom, m, 3) << " := " << (phase ? "true" : "false") << "\n");

                    auto const& activities = ctx->get_activity_vector();
                    double max_activity = 0.0;
                    for (unsigned i = 0; i < activities.size(); ++i)
                        max_activity = std::max(max_activity, activities[i]);

                    original_activities.insert(v, ctx->get_activity(v));

                    // Promote this candidate above all others
                    double eps = 1.0;
                    ctx->set_activity(v, max_activity + eps);

                    LOG_WORKER(2, " boosted activity of backbone candidate to " << (max_activity + eps) << "\n");
                }

                if (m_config.m_global_backbones)
                    b.collect_backbone_candidates(m_l2g, backbone_candidates);

                if (!m.inc()) {
                    b.set_exception("context cancelled");
                    return;
                }
            }

            lbool r = check_cube(cube);

            if (!m.inc()) {
                b.set_exception("context cancelled");
                return;
            }

            if (m_config.m_local_backbones) {
                // Restore activities of backbone candidates to old values after the search
                for (auto const& [v, act] : original_activities) {
                    ctx->set_activity(v, act);
                    ctx->unforce_phase(v); // can do ablation study here to see if it's necessary
                }
            }

            switch (r) {
            case l_undef: {
                update_max_thread_conflicts();
                LOG_WORKER(1, " found undef cube\n");
                if (m_config.m_max_cube_depth <= cube.size())
                    goto check_cube_start;

                auto atom = get_split_atom();
                if (!atom)
                    goto check_cube_start;
                b.split(m_l2g, id, node, atom);
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
                expr_ref_vector const &unsat_core = ctx->unsat_core();
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
                b.backtrack(m_l2g, unsat_core, node);

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
        ctx->m_phase_cache_on = true; // not sure if this is needed, ensure phase caching is on for backbone detection for now

        smt_parallel_params pp(p.ctx.m_params);
        m_config.m_inprocessing = pp.inprocessing();
        m_config.m_global_backbones = pp.global_backbones();
        m_config.m_local_backbones = pp.local_backbones();
    }

    parallel::sls_worker::sls_worker(parallel& p)
        : p(p), b(p.m_batch_manager), m(), m_g2l(p.ctx.m, m), m_l2g(m, p.ctx.m) {
        IF_VERBOSE(1, verbose_stream() << "Initialized SLS portfolio thread\n");
        m_params.append(p.ctx.m_params);
        m_sls = alloc(sls::smt_solver, m, m_params);
    }

    parallel::backbones_worker::backbones_worker(parallel &p, expr_ref_vector const &_asms)
        : b(p.m_batch_manager), m(), asms(m), m_smt_params(p.ctx.get_fparams()), m_g2l(p.ctx.m, m), m_l2g(m, p.ctx.m) {
        for (auto e : _asms)
            asms.push_back(m_g2l(e));
        IF_VERBOSE(1, verbose_stream() << "Initialized backbones thread\n");
        ctx = alloc(context, m, m_smt_params, p.ctx.get_params());
        ctx->set_logic(p.ctx.m_setup.get_logic());
        context::copy(p.ctx, *ctx, true);
    }

    svector<smt::parallel::bb_candidate> parallel::worker::find_backbone_candidates(unsigned k) {
        svector<smt::parallel::bb_candidate> backbone_candidates;
        vector<std::pair<double, expr_ref>> top_k; // will hold at most k elements
        expr_ref candidate(m);
        unsigned curr_time = ctx->m_stats.m_num_assignments;

        for (bool_var v = 0; v < ctx->get_num_bool_vars(); ++v) {
            if (ctx->get_assignment(v) != l_undef) 
                continue;

            auto const& d = ctx->get_bdata(v);
            if (!d.m_phase_available)
                continue;

            unsigned birth = ctx->m_birthdate[v];
            unsigned age = curr_time - birth;

            bool phase = d.m_phase;

            candidate = ctx->bool_var2expr(v);
            if (!candidate)
                continue;

            if (!phase)
                candidate = m.mk_not(candidate);

            if (b.is_global_backbone(candidate))
                continue;

            double score = age;

            // insert into top_k. linear scan since k is very small
            if (top_k.size() < k) {
                top_k.push_back({score, candidate});
            } 
            else {
                // find the smallest in top_k and replace if we found a new element bigger than the min
                size_t min_idx = 0;
                for (size_t i = 1; i < k; ++i)
                    if (top_k[i].first < top_k[min_idx].first)
                        min_idx = i;

                if (score > top_k[min_idx].first) {
                    top_k[min_idx] = {score, candidate};
                }
            }
        }

        for (auto& p : top_k)
            backbone_candidates.push_back(bb_candidate(m, p.second.get(), p.first, 1));
        
        return backbone_candidates;
    }

    // 
    // Assume the negation of all candidates (or a batch of them)
    // run the solver with a low budget of conflicts
    // if the unsat core contains a single candidate we have found a backbone literal
    // 
    bool parallel::backbones_worker::check_backbone(expr_ref const& bb_candidate) {
        unsigned sz = asms.size();
        asms.push_back(m.mk_not(bb_candidate.get()));
        ctx->get_fparams().m_max_conflicts = 2000;
        
        lbool r = l_undef;
        try {
            r = ctx->check(asms.size(), asms.data());
        }
        catch (z3_error& err) {
            b.set_exception(err.error_code());
        }
        catch (z3_exception& ex) {
            b.set_exception(ex.what());
        }
        catch (...) {
            b.set_exception("unknown exception");
        }

        asms.shrink(sz);

        IF_VERBOSE(1, verbose_stream() << " BACKBONE CHECK RESULT: " << r << " FOR CANDIDATE: " << mk_bounded_pp(bb_candidate.get(), m, 3) << "\n");

        if (r == l_false) {
            auto core = ctx->unsat_core();
            if (core.size() == 1) {
                return true;
            }                
        }

        return false;
    }

    expr_ref_vector parallel::backbones_worker::check_backbone_batch(svector<bb_candidate> const& candidates) {
        expr_ref_vector likely_backbones(m);
        unsigned base_sz = asms.size();
        ctx->get_fparams().m_max_conflicts = 1000;

        expr_ref_vector backbone_asms(m);
        for (auto const& c : candidates) {
            expr_ref a(mk_not(m, c.lit.get()), m);
            backbone_asms.push_back(a);
            asms.push_back(a);
        }

        lbool r = l_undef;
        try {
            r = ctx->check(asms.size(), asms.data());
        }
        catch (z3_error& err) {
            b.set_exception(err.error_code());
        }
        catch (z3_exception& ex) {
            b.set_exception(ex.what());
        }
        catch (...) {
            b.set_exception("unknown exception");
        }

        asms.shrink(base_sz);

        IF_VERBOSE(1, verbose_stream() << " BACKBONE BATCH CHECK RESULT: " << r << "\n");

        if (r == l_false) {
            expr_ref_vector core = ctx->unsat_core();

            IF_VERBOSE(1, verbose_stream() << "BACKBONE BATCH UNSAT CORE SIZE: " << core.size() << "\n");

            for (expr* a : core) {
                if (backbone_asms.contains(a)) { // make sure we're not including external assumptions that are not backbone candidates
                    expr* backbone = mk_not(m, a); // core contains assumption literal: ¬c, negate to get the backbone candidate c
                    likely_backbones.push_back(backbone);
                }
            }
        }

        return likely_backbones;
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
                e = m.mk_not(e);  // negate if literal is negative
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
    }

    void parallel::worker::cancel() {
        LOG_WORKER(1, " canceling\n");
        m.limit().cancel();
    }

    void parallel::batch_manager::backtrack(ast_translation &l2g, expr_ref_vector const &core,
                                            search_tree::node<cube_config> *node) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager backtracking.\n");
        if (m_state != state::is_running)
            return;
        vector<cube_config::literal> g_core;
        for (auto c : core) {
            expr_ref g_c(l2g(c), m);
            g_core.push_back(expr_ref(l2g(c), m));
        }
        m_search_tree.backtrack(node, g_core);

        IF_VERBOSE(1, m_search_tree.display(verbose_stream() << bounded_pp_exprs(core) << "\n"););
        if (m_search_tree.is_closed()) {
            IF_VERBOSE(1, verbose_stream() << "Search tree closed, setting UNSAT\n");
            m_state = state::is_unsat;
            SASSERT(p.ctx.m_unsat_core.empty());
            for (auto e : m_search_tree.get_core_from_root())
               p.ctx.m_unsat_core.push_back(e);
            cancel_background_threads();
        }
    }

    void parallel::batch_manager::split(ast_translation &l2g, unsigned source_worker_id,
                                        search_tree::node<cube_config> *node, expr *atom) {
        std::scoped_lock lock(mux);
        expr_ref lit(m), nlit(m);
        lit = l2g(atom);
        nlit = mk_not(m, lit);
        IF_VERBOSE(1, verbose_stream() << "Batch manager splitting on literal: " << mk_bounded_pp(lit, m, 3) << "\n");
        if (m_state != state::is_running)
            return;
        // optional heuristic:
        // node->get_status() == status::active
        // and depth is 'high' enough
        // then ignore split, and instead set the status of node to open.
        ++m_stats.m_num_cubes;
        m_stats.m_max_cube_depth = std::max(m_stats.m_max_cube_depth, node->depth() + 1);
        m_search_tree.split(node, lit, nlit);
    }

    void parallel::batch_manager::collect_clause(ast_translation &l2g, unsigned source_worker_id, expr *clause) {
        std::scoped_lock lock(mux);
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

    void parallel::batch_manager::collect_backbone_candidates(ast_translation& l2g, svector<smt::parallel::bb_candidate>& bb_candidates) {
        std::scoped_lock lock(mux);

        auto find_existing_candidate_idx = [&](expr* e) -> int {
            for (unsigned i = 0; i < m_bb_candidates.size(); ++i) {
                if (m_bb_candidates[i].lit.get() == e)
                    return i;
            }
            return -1;
        };

        auto rank_of = [&](bb_candidate const& c) {
            return c.score * std::log2(2.0 + c.hits);
        };

        for (auto const& c : bb_candidates) {
            expr_ref g_lit(l2g(c.lit.get()), m);
            if (is_global_backbone(g_lit.get()))
                continue;

            double score = c.score;
            int idx = find_existing_candidate_idx(g_lit.get());

            if (idx >= 0) {
                auto& existing = m_bb_candidates[idx];
                existing.score = (existing.score * existing.hits + score) / (existing.hits + 1);
                existing.hits++;
                continue;
            }

            if (m_bb_candidates.size() < m_bb_max) {
                m_bb_candidates.push_back(bb_candidate(m, g_lit.get(), score, 1));
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

            bb_candidate new_bb_candidate = bb_candidate(m, g_lit.get(), score, 1);
            if (rank_of(new_bb_candidate) > worst_rank)
                m_bb_candidates[worst_idx] = new_bb_candidate;
        }

        if (!m_bb_candidates.empty())
            m_bb_cv.notify_one();
    }

    bool parallel::batch_manager::wait_for_backbone_job(
        ast_translation& g2l,
        svector<smt::parallel::bb_candidate>& out,
        reslimit& lim)
    {
        out.reset();
        std::unique_lock<std::mutex> lock(mux);

        // Wait until there is something to check
        m_bb_cv.wait(lock, [&]() {
            return m_bb_stop ||
                lim.is_canceled() ||
                m_state != state::is_running ||
                !m_bb_candidates.empty();
        });

        // Exit conditions
        if (lim.is_canceled())
            return false;

        if (m_bb_stop || m_state != state::is_running)
            return false;

        if (m_bb_candidates.empty())
            return true; // spurious wakeup

        // -------------------------------------------------
        // TAKE the entire candidate pool and RESET it
        // -------------------------------------------------
        out = std::move(m_bb_candidates);
        m_bb_candidates.reset();

        // Translate GLOBAL -> LOCAL for the backbone thread
        for (auto& c : out) {
            expr_ref l_lit(g2l(c.lit.get()), g2l.to());
            c.lit = l_lit;
        }

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
            b.set_exception(err.error_code());
        } catch (z3_exception &ex) {
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
            if (b.is_global_backbone(e) || b.is_global_backbone(m.mk_not(e)))
                continue;

            double new_score = ctx->m_lit_scores[0][v] * ctx->m_lit_scores[1][v];

            ctx->m_lit_scores[0][v] /= 2;
            ctx->m_lit_scores[1][v] /= 2;

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

    bool parallel::batch_manager::get_cube(ast_translation &g2l, unsigned id, expr_ref_vector &cube, node *&n) {
        cube.reset();
        std::unique_lock<std::mutex> lock(mux);
        if (m_search_tree.is_closed()) {
            IF_VERBOSE(1, verbose_stream() << "all done\n";);
            return false;
        }
        if (m_state != state::is_running) {
            IF_VERBOSE(1, verbose_stream() << "aborting get_cube\n";);
            return false;
        }
        node *t = m_search_tree.activate_node(n);
        if (!t)
            t = m_search_tree.find_active_node();
        if (!t)
            return false;
        IF_VERBOSE(1, m_search_tree.display(verbose_stream()); verbose_stream() << "\n";);
        n = t;
        while (t) {
            if (cube_config::literal_is_null(t->get_literal()))
                break;
            expr_ref lit(g2l.to());
            lit = g2l(t->get_literal().get());
            cube.push_back(lit);
            t = t->parent();
        }
        return true;
    }

    void parallel::batch_manager::initialize() {
        m_state = state::is_running;
        m_bb_stop = false;
        m_search_tree.reset();
        m_bb_candidates.reset();
    }

    void parallel::batch_manager::collect_statistics(::statistics &st) const {
        st.update("parallel-num_cubes", m_stats.m_num_cubes);
        st.update("parallel-max-cube-size", m_stats.m_max_cube_depth);
    }

    lbool parallel::operator()(expr_ref_vector const &asms) {
        IF_VERBOSE(1, verbose_stream() << "Parallel SMT with " << num_workers << " threads\n";);
        ast_manager &m = ctx.m;

        if (m.has_trace_stream())
            throw default_exception("trace streams have to be off in parallel mode");

        struct scoped_clear {
            parallel &p;
            scoped_clear(parallel &p) : p(p) {}
            ~scoped_clear() {
                p.m_workers.reset();
                p.m_sls_worker = nullptr;
            }
        };
        scoped_clear clear(*this);

        m_batch_manager.initialize();
        m_workers.reset();

        smt_parallel_params pp(ctx.m_params);
        m_should_run_sls = pp.sls();
        m_should_run_global_backbones = pp.global_backbones();
        
        scoped_limits sl(m.limit());
        flet<unsigned> _nt(ctx.m_fparams.m_threads, 1);
        SASSERT(num_workers > 1);
        for (unsigned i = 0; i < num_workers; ++i)
            m_workers.push_back(alloc(worker, i, *this, asms));
        for (auto w : m_workers)
            sl.push_child(&(w->limit()));
        if (m_should_run_sls) {
            m_sls_worker = alloc(sls_worker, *this);
            sl.push_child(&(m_sls_worker->limit()));
        }
        if (m_should_run_global_backbones) {
            m_global_backbones_worker = alloc(backbones_worker, *this, asms);
            sl.push_child(&(m_global_backbones_worker->limit()));
        }

        // Launch threads
        vector<std::thread> threads;
        unsigned total_threads = num_workers + (m_should_run_sls ? 1 : 0) + (m_should_run_global_backbones ? 1 : 0);
        threads.resize(total_threads);
        unsigned thread_idx = 0;
        for (unsigned i = 0; i < num_workers; ++i) {
            threads[thread_idx++] = std::thread([&, i]() { m_workers[i]->run(); });
        }
        
        if (m_should_run_sls)
            threads[thread_idx++] = std::thread([&]() { m_sls_worker->run(); });
        if (m_should_run_global_backbones)
            threads[thread_idx++] = std::thread([&]() { m_global_backbones_worker->run(); });

        // Wait for all threads to finish
        for (auto &th : threads)
            th.join();

        for (auto w : m_workers)
            w->collect_statistics(ctx.m_aux_stats);
        m_batch_manager.collect_statistics(ctx.m_aux_stats);
        if (m_should_run_sls)
            m_sls_worker->collect_statistics(ctx.m_aux_stats);
        if (m_should_run_global_backbones)
            m_global_backbones_worker->collect_statistics(ctx.m_aux_stats);

        return m_batch_manager.get_result();
    }

}  // namespace smt
#endif
