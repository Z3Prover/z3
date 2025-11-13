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

    lbool parallel::param_generator::run_prefix_step() {
        if (m.limit().is_canceled())
            return l_undef;
        IF_VERBOSE(1, verbose_stream() << " PARAM TUNER running prefix step with conflicts " << m_max_prefix_conflicts <<"\n");
        ctx->get_fparams().m_max_conflicts = m_max_prefix_conflicts;
        ctx->get_fparams().m_threads = 1;

        m_recorded_cubes.reset();
        ctx->m_recorded_cubes = &m_recorded_cubes;
        lbool r = l_undef;
        try {
            r = ctx->check(0, nullptr, true);
            IF_VERBOSE(1, verbose_stream() << " PARAM TUNER: prefix step result " << r << "\n");
        } 
        catch (z3_error &err) {
            b.set_exception(err.error_code());
        } 
        catch (z3_exception &ex) {
            b.set_exception(ex.what());
        } 
        catch (...) {
            b.set_exception("unknown exception");
        }
        return r;
    }

    void parallel::param_generator::replay_proof_prefixes(unsigned max_conflicts_epsilon=200) {
        unsigned conflict_budget = m_max_prefix_conflicts + max_conflicts_epsilon;
        param_values best_param_state;
        double best_score = 0;
        bool found_better_params = false;

        for (unsigned i = 0; i <= N; ++i) {
            if (m.limit().is_canceled())
              return;

            IF_VERBOSE(1, verbose_stream() << " PARAM TUNER: replaying proof prefix in param probe context " << i << "\n");
            
            // copy prefix solver context to a new probe_ctx for next replay with candidate mutation
            smt_params smtp(m_p);
            scoped_ptr<context> probe_ctx = alloc(context, m, smtp, m_p);
            context::copy(*ctx, *probe_ctx, true);

            // apply a candidate (mutated) param state to probe_ctx
            // (except for the first iteration, use the current param state)
            param_values mutated_param_state = m_param_state;
            if (i > 0) {
                mutated_param_state = mutate_param_state();
                params_ref p = apply_param_values(mutated_param_state);
                probe_ctx->updt_params(p);
            }

            probe_ctx->get_fparams().m_max_conflicts = conflict_budget;
            probe_ctx->get_fparams().m_threads = 1;

            // replay the cube (negation of the clause)
            IF_VERBOSE(1, verbose_stream() << " PARAM TUNER: begin replay of " << m_recorded_cubes.size() << " cubes\n");
            for (expr_ref_vector const& cube : m_recorded_cubes) {
                if (m.limit().is_canceled())
                  return;
                // the conflicts and decisions are cumulative over all cube replays inside the probe_ctx
                lbool r = probe_ctx->check(cube.size(), cube.data(), true);               
                IF_VERBOSE(2, verbose_stream() << " PARAM TUNER " << i << ": cube replay result " << r << "\n");                
            }
            unsigned conflicts = probe_ctx->m_stats.m_num_conflicts;
            unsigned decisions = probe_ctx->m_stats.m_num_decisions;
            double score = conflicts + decisions;

            if (i == 0) {
                best_score = score;
                IF_VERBOSE(1, verbose_stream() << " PARAM TUNER: baseline score = " << best_score << "\n");
            }
            else if (score < best_score) {
                found_better_params = true;
                best_param_state = mutated_param_state;                
                best_score = score;
            }
        }
        
        if (found_better_params) {
            m_param_state = best_param_state;
            auto p = apply_param_values(m_param_state);
            b.set_param_state(p);
            IF_VERBOSE(1, verbose_stream() << " PARAM TUNER found better param state:\n");
            print_param_values(m_param_state);
        }
        else {
            IF_VERBOSE(1, verbose_stream() << " PARAM TUNER retained current param state\n");
        }
    }

    void parallel::param_generator::init_param_state() {
        smt_params_helper smtp(m_p);
        m_param_state.push_back({symbol("smt.arith.nl.branching"), smtp.arith_nl_branching()});
        m_param_state.push_back({symbol("smt.arith.nl.cross_nested"), smtp.arith_nl_cross_nested()});
        m_param_state.push_back({symbol("smt.arith.nl.delay"), unsigned_value({smtp.arith_nl_delay(), 5, 10})});
        m_param_state.push_back({symbol("smt.arith.nl.expensive_patching"), smtp.arith_nl_expensive_patching()});
        m_param_state.push_back({symbol("smt.arith.nl.gb"), smtp.arith_nl_grobner()});
        m_param_state.push_back({symbol("smt.arith.nl.horner"), smtp.arith_nl_horner()});
        m_param_state.push_back({symbol("smt.arith.nl.horner_frequency"), unsigned_value({smtp.arith_nl_horner_frequency(), 2, 6})});
        m_param_state.push_back({symbol("smt.arith.nl.optimize_bounds"), smtp.arith_nl_optimize_bounds()});
        m_param_state.push_back({symbol("smt.arith.nl.propagate_linear_monomials"), smtp.arith_nl_propagate_linear_monomials()});
        m_param_state.push_back({symbol("smt.arith.nl.tangents"), smtp.arith_nl_tangents()});
    };

    params_ref parallel::param_generator::apply_param_values(param_values const &pv) {
        params_ref p = m_p.clone();
        for (auto const &[k, v] : pv) {
            if (std::holds_alternative<unsigned_value>(v)) {
                unsigned_value uv = std::get<unsigned_value>(v);
                p.set_uint(k, uv.value);
            }
            else if (std::holds_alternative<bool>(v)) {
                bool bv = std::get<bool>(v);
                p.set_bool(k, bv);
            }
        }
        return p;
    }

    parallel::param_generator::param_values parallel::param_generator::mutate_param_state() {
        param_values new_param_values(m_param_state);
        unsigned index = ctx->get_random_value() % new_param_values.size();
        auto &param = new_param_values[index];
        if (std::holds_alternative<bool>(param.second)) {
            bool& value = std::get<bool>(param.second);
            value = !value;
        } 
        else if (std::holds_alternative<unsigned_value>(param.second)) {
            auto [value, lo, hi] = std::get<unsigned_value>(param.second);
            unsigned new_value = value;
            while (new_value == value) {
                new_value = lo + ctx->get_random_value() % (hi - lo + 1);
            }
            std::get<unsigned_value>(param.second).value = new_value;
        }
        IF_VERBOSE(1, 
            verbose_stream() << "Mutating param: ";
            for (auto const &[name, val] : new_param_values) {
                if (std::holds_alternative<bool>(val)) {
                    verbose_stream() << name << " = " << std::get<bool>(val) << "\n";
                } 
                else if (std::holds_alternative<unsigned_value>(val)) {
                    verbose_stream() << name << " = " << std::get<unsigned_value>(val).value << "\n";
                }
            }
            );
        return new_param_values;
    }

    void parallel::param_generator::protocol_iteration() {
        while (!m.limit().is_canceled()) {
            IF_VERBOSE(1, verbose_stream() << " PARAM TUNER running protocol iteration\n");
            
            ctx->get_fparams().m_max_conflicts = m_max_prefix_conflicts;
            lbool r = run_prefix_step();

            if (m.limit().is_canceled())
                return;

            switch (r) {
                case l_undef: {
                    replay_proof_prefixes();
                    break;
                }
                case l_true: {
                    IF_VERBOSE(1, verbose_stream() << " PARAM TUNER found formula sat\n");
                    model_ref mdl;
                    ctx->get_model(mdl);
                    b.set_sat(m_l2g, *mdl);
                    break;
                }
                case l_false: {
                    expr_ref_vector const &unsat_core = ctx->unsat_core();
                    IF_VERBOSE(2, verbose_stream() << " unsat core:\n";
                              for (auto c : unsat_core) verbose_stream() << mk_bounded_pp(c, m, 3) << "\n");
                    IF_VERBOSE(1, verbose_stream() << " PARAM TUNER determined formula unsat\n");
                    b.set_unsat(m_l2g, unsat_core);
                    break;
                }
            }
        }
    }

    void parallel::param_generator::cancel() {
        IF_VERBOSE(1, verbose_stream() << " PARAM TUNER cancelling\n");
        m.limit().cancel();
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
            
            // apply current best param state from batch manager
            params_ref p;
            b.get_param_state(p);           
            ctx->updt_params(p);

            lbool r = check_cube(cube);

            if (m.limit().is_canceled()) {
                b.set_exception("context cancelled");
                return;
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
                break;
            }
            }
            if (m_config.m_share_units)
                share_units();
        }
    }

    parallel::worker::worker(unsigned id, parallel &p, expr_ref_vector const &_asms)
        : id(id), p(p), b(p.m_batch_manager), m_smt_params(p.ctx.get_fparams()), asms(m), m_g2l(p.ctx.m, m),
          m_l2g(m, p.ctx.m) {
        for (auto e : _asms)
            asms.push_back(m_g2l(e));
        LOG_WORKER(1, " created with " << asms.size() << " assumptions\n");
        m_smt_params.m_preprocess = false;
        ctx = alloc(context, m, m_smt_params, p.ctx.get_params());
        context::copy(p.ctx, *ctx, true);
        ctx->set_random_seed(id + m_smt_params.m_random_seed);
        // don't share initial units
        ctx->pop_to_base_lvl();
        m_num_shared_units = ctx->assigned_literals().size();
        m_num_initial_atoms = ctx->get_num_bool_vars();
    }

    parallel::param_generator::param_generator(parallel& p)
        : b(p.m_batch_manager), m_p(p.ctx.get_params()), m_l2g(m, p.ctx.m) {

        m.copy_families_plugins(p.ctx.m);
        SASSERT(p.ctx.get_fparams().m_threads == 1);
        ctx = alloc(context, m, p.ctx.get_fparams(), m_p);
        context::copy(p.ctx, *ctx, true);
        // don't share initial units
        ctx->pop_to_base_lvl();
        init_param_state();
        IF_VERBOSE(1, verbose_stream() << "Initialized parameter generator\n");
    }

    void parallel::worker::share_units() {
        // Collect new units learned locally by this worker and send to batch manager
        ctx->pop_to_base_lvl();
        unsigned sz = ctx->assigned_literals().size();
        for (unsigned j = m_num_shared_units; j < sz; ++j) {  // iterate only over new literals since last sync
            literal lit = ctx->assigned_literals()[j];
            if (!ctx->is_relevant(lit.var()) && m_config.m_share_units_relevant_only)
                continue;

            if (m_config.m_share_units_initial_only && lit.var() >= m_num_initial_atoms) {
                LOG_WORKER(2, " Skipping non-initial unit: " << lit.var() << "\n");
                continue;  // skip non-iniial atoms if configured to do so
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
            m_state = state::is_unsat;
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

    void parallel::batch_manager::get_param_state(params_ref& p) {
        std::scoped_lock lock(mux);
        p.copy(m_param_state);
    }

    void parallel::worker::collect_shared_clauses() {
        expr_ref_vector new_clauses = b.return_shared_clauses(m_g2l, m_shared_clause_limit, id);
        // iterate over new clauses and assert them in the local context
        for (expr *e : new_clauses) {
            ctx->assert_expr(e);
            LOG_WORKER(2, " asserting shared clause: " << mk_bounded_pp(e, m, 3) << "\n");
        }
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
            r = ctx->check(asms.size(), asms.data(), true);
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
        m_search_tree.reset();
    }

    void parallel::batch_manager::collect_statistics(::statistics &st) const {
        st.update("parallel-num_cubes", m_stats.m_num_cubes);
        st.update("parallel-max-cube-size", m_stats.m_max_cube_depth);
    }

    lbool parallel::operator()(expr_ref_vector const &asms) {
        ast_manager &m = ctx.m;

        if (m.has_trace_stream())
            throw default_exception("trace streams have to be off in parallel mode");

        struct scoped_clear {
            parallel &p;
            scoped_clear(parallel &p) : p(p) {}
            ~scoped_clear() {
                p.m_workers.reset();
                p.m_param_generator = nullptr;
            }
        };
        scoped_clear clear(*this);

        m_batch_manager.initialize();
        m_workers.reset();

        smt_parallel_params pp(ctx.m_params);
        m_should_tune_params = pp.param_tuning();
        m_should_run_parallel = pp.enable_parallel_smt();
        
        scoped_limits sl(m.limit());
        flet<unsigned> _nt(ctx.m_fparams.m_threads, 1);

        if (m_should_run_parallel) {
            SASSERT(num_threads > 1);
            for (unsigned i = 0; i < num_threads; ++i)
                m_workers.push_back(alloc(worker, i, *this, asms));
            
            for (auto w : m_workers)
                sl.push_child(&(w->limit()));
        }

        if (m_should_tune_params) {
            m_param_generator = alloc(param_generator, *this);
            sl.push_child(&(m_param_generator->limit()));
        }

        std::string tuned = pp.tunable_params();
        if (!tuned.empty()) {
            auto trim = [](std::string &s) {
                s.erase(0, s.find_first_not_of(" \t\n\r"));
                s.erase(s.find_last_not_of(" \t\n\r") + 1);
            };

            std::stringstream ss(tuned);
            std::string kv;

            while (std::getline(ss, kv, ',')) {
                size_t eq = kv.find('=');
                if (eq == std::string::npos)
                    continue;

                std::string key = kv.substr(0, eq);
                std::string val = kv.substr(eq + 1);
                trim(key);
                trim(val);

                if (val == "true" || val == "1") {
                    ctx.m_params.set_bool(symbol(key.c_str()), true);
                }
                else if (val == "false" || val == "0") {
                    ctx.m_params.set_bool(symbol(key.c_str()), false);
                }
                else if (std::all_of(val.begin(), val.end(), ::isdigit)) {
                    ctx.m_params.set_uint(symbol(key.c_str()),
                        static_cast<unsigned>(std::stoul(val)));
                } else {
                  IF_VERBOSE(1, 
                    verbose_stream() << "Ignoring invalid parameter override: " << kv << "\n";);
                }
            }

            IF_VERBOSE(1, 
                verbose_stream() << "Applied parameter overrides:\n";
                ctx.m_params.display(verbose_stream());
            );
        }

        // Launch threads
        // threads must live beyond the branch scope so we declare them here.
        vector<std::thread> threads;
        if (m_should_run_parallel) {
            threads.resize(m_should_tune_params ? num_threads + 1 : num_threads); // +1 for param generator
            for (unsigned i = 0; i < num_threads; ++i) {
                threads[i] = std::thread([&, i]() { m_workers[i]->run(); });
            }
            // the final thread runs the parameter generator
            if (m_should_tune_params) {
                threads[num_threads] = std::thread([&]() { m_param_generator->protocol_iteration(); });
            }
        } else { // just do param tuning (if requested)
            if (m_should_tune_params) {
              threads.resize(1);
              threads[0] = std::thread([&]() { m_param_generator->protocol_iteration(); });
            }
        }

        // Wait for all threads to finish
        for (auto &th : threads)
            th.join();

        for (auto w : m_workers)
            w->collect_statistics(ctx.m_aux_stats);
        m_batch_manager.collect_statistics(ctx.m_aux_stats);

        return m_batch_manager.get_result();
    }

}  // namespace smt
#endif
