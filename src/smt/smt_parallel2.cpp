/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_parallel.cpp

Abstract:

    Parallel SMT, portfolio loop specialized to SMT core.

Author:

    nbjorner 2020-01-31

--*/




#include "util/scoped_ptr_vector.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_translation.h"
#include "ast/simplifiers/then_simplifier.h"
#include "smt/smt_parallel2.h"
#include "smt/smt_lookahead.h"
#include "params/smt_parallel_params.hpp"
#include "solver/solver_preprocess.h"

#include <cmath>
#include <condition_variable>
#include <mutex>

class bounded_pp_exprs {
    expr_ref_vector const& es;
public:
    bounded_pp_exprs(expr_ref_vector const& es): es(es) {}

    std::ostream& display(std::ostream& out) const {
        for (auto e : es) 
            out << mk_bounded_pp(e, es.get_manager()) << "\n";
        return out;
    }
};

inline std::ostream& operator<<(std::ostream& out, bounded_pp_exprs const& pp) {
    return pp.display(out);
}

#ifdef SINGLE_THREAD

namespace smt {
    
    lbool parallel2::operator()(expr_ref_vector const& asms) {
        return l_undef;
    }
}

#else

#include <thread>
#include <mutex>
#include <condition_variable>

#define SHARE_SEARCH_TREE 1

#define LOG_WORKER(lvl, s) IF_VERBOSE(lvl, verbose_stream() << "Worker " << id << s)

namespace smt {

 

    void parallel2::worker::run() {
        search_tree::node<cube_config>* node = nullptr;
        expr_ref_vector cube(m);
        while (true) { 


#if SHARE_SEARCH_TREE
            if (!b.get_cube(m_g2l, id, cube, node)) {
                LOG_WORKER(1, " no more cubes\n");
                return;
            }
#else
            if (!get_cube(cube, node))
                return;
#endif
            collect_shared_clauses(m_g2l);

        check_cube_start:
            LOG_WORKER(1, " CUBE SIZE IN MAIN LOOP: " << cube.size() << "\n");
            lbool r = check_cube(cube);

            if (!m.inc()) {
                b.set_exception("context cancelled");
                return;
            }
            
            switch (r) {
                case l_undef: {
                    update_max_thread_conflicts();
                    LOG_WORKER(1, " found undef cube\n");
                    // return unprocessed cubes to the batch manager
                    // add a split literal to the batch manager.
                    // optionally process other cubes and delay sending back unprocessed cubes to batch manager.
                    if (m_config.m_max_cube_depth <= cube.size()) 
                        goto check_cube_start;

                    auto atom = get_split_atom();
                    if (!atom)
                        goto check_cube_start;
#if SHARE_SEARCH_TREE
                    b.split(m_l2g, id, node, atom);
#else
                    split(node, atom);
#endif
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
                    expr_ref_vector const& unsat_core = ctx->unsat_core();
                    LOG_WORKER(2, " unsat core:\n"; for (auto c : unsat_core) verbose_stream() << mk_bounded_pp(c, m, 3) << "\n");
                    // If the unsat core only contains external assumptions, 
                    // unsatisfiability does not depend on the current cube and the entire problem is unsat.
                    if (all_of(unsat_core, [&](expr* e) { return asms.contains(e); })) {
                        LOG_WORKER(1, " determined formula unsat\n");
                        b.set_unsat(m_l2g, unsat_core);
                        return;
                    }
                    for (expr* e : unsat_core)
                        if (asms.contains(e))
                            b.report_assumption_used(m_l2g, e); // report assumptions used in unsat core, so they can be used in final core

                    LOG_WORKER(1, " found unsat cube\n");    
#if SHARE_SEARCH_TREE
                    b.backtrack(m_l2g, unsat_core, node);
#else
                    backtrack(unsat_core, node);
#endif
                    break;
                }
            }    
            if (m_config.m_share_units)
                share_units(m_l2g);
        }
    }

    bool parallel2::worker::get_cube(expr_ref_vector& cube, node*& n) {
        node* t = m_search_tree.activate_node(n);
        cube.reset();
        if (!t) {
            b.set_unsat(m_l2g, cube);
            return false;
        }
        n = t;
        while (t) {
            if (cube_config::literal_is_null(t->get_literal()))
                break;
            cube.push_back(t->get_literal());
            t = t->parent();
        }
        return true;
    }

    void parallel2::worker::backtrack(expr_ref_vector const& core, node* n) {
        vector<expr_ref> core_copy;
        for (auto c : core)
            core_copy.push_back(expr_ref(c, m));
        m_search_tree.backtrack(n, core_copy);
        //LOG_WORKER(1, m_search_tree.display(verbose_stream() << bounded_pp_exprs(core) << "\n"););
    }

    void parallel2::worker::split(node* n, expr* atom) {
        expr_ref lit(atom, m), nlit(m);
        nlit = mk_not(m, lit);
        IF_VERBOSE(1, verbose_stream() << "Batch manager splitting on literal: " << mk_bounded_pp(lit, m, 3) << "\n");
        m_search_tree.split(n, lit, nlit);
    }

    parallel2::worker::worker(unsigned id, parallel2& p, expr_ref_vector const& _asms): 
        id(id), p(p), b(p.m_batch_manager), m_smt_params(p.ctx.get_fparams()), asms(m),
        m_g2l(p.ctx.m, m),
        m_l2g(m, p.ctx.m),
        m_search_tree(expr_ref(m)) {
        for (auto e : _asms) 
            asms.push_back(m_g2l(e));
        LOG_WORKER(1, " created with " << asms.size() << " assumptions\n");        
        m_smt_params.m_preprocess = false;
        ctx = alloc(context, m, m_smt_params, p.ctx.get_params());
        context::copy(p.ctx, *ctx, true);
        ctx->set_random_seed(id + m_smt_params.m_random_seed);
        
        smt_parallel_params pp(p.ctx.m_params);
        m_config.m_threads_max_conflicts = ctx->get_fparams().m_threads_max_conflicts;
        m_config.m_max_conflicts = ctx->get_fparams().m_max_conflicts;
        m_config.m_relevant_units_only = pp.relevant_units_only();
        m_config.m_never_cube = pp.never_cube();
        m_config.m_share_conflicts = pp.share_conflicts();
        m_config.m_share_units = pp.share_units();
        m_config.m_share_units_initial_only = pp.share_units_initial_only();
        m_config.m_cube_initial_only = pp.cube_initial_only();
        m_config.m_max_conflict_mul = pp.max_conflict_mul();
        m_config.m_max_greedy_cubes = pp.max_greedy_cubes();
        m_config.m_num_split_lits = pp.num_split_lits();
        m_config.m_backbone_detection = pp.backbone_detection();
        m_config.m_iterative_deepening = pp.iterative_deepening();
        m_config.m_beam_search = pp.beam_search();
        m_config.m_explicit_hardness = pp.explicit_hardness();
        m_config.m_cubetree = pp.cubetree();
        m_config.m_max_cube_depth = pp.max_cube_depth();
        m_config.m_inprocessing = pp.inprocessing();
        m_config.m_inprocessing_delay = pp.inprocessing_delay();

        // don't share initial units
        ctx->pop_to_base_lvl();
        m_num_shared_units = ctx->assigned_literals().size();

        m_num_initial_atoms = ctx->get_num_bool_vars();
    }

    void parallel2::worker::share_units(ast_translation& l2g) {
        // Collect new units learned locally by this worker and send to batch manager
        ctx->pop_to_base_lvl();
        unsigned sz = ctx->assigned_literals().size();
        for (unsigned j = m_num_shared_units; j < sz; ++j) {  // iterate only over new literals since last sync
            literal lit = ctx->assigned_literals()[j];
            if (!ctx->is_relevant(lit.var()) && m_config.m_relevant_units_only) 
                continue;

            if (m_config.m_share_units_initial_only && lit.var() >= m_num_initial_atoms) {
                LOG_WORKER(2, " Skipping non-initial unit: " << lit.var() << "\n");
                continue; // skip non-iniial atoms if configured to do so
            }
            
            expr_ref e(ctx->bool_var2expr(lit.var()), ctx->m); // turn literal into a Boolean expression
            if (m.is_and(e) || m.is_or(e))             
                continue;

            if (lit.sign())
                e = m.mk_not(e); // negate if literal is negative
            b.collect_clause(l2g, id, e);
        }
        m_num_shared_units = sz;
    }



    void parallel2::worker::simplify() {
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
        m_config.m_inprocessing = false; // initial strategy is to immediately disable inprocessing for future calls.
        dependent_expr_simplifier* s = ctx->m_simplifier.get();
        if (!s) {
            // create a simplifier if none exists
            // initialize it to a default pre-processing simplifier.
            ctx->m_fmls = alloc(base_dependent_expr_state, m);
            auto then_s = alloc(then_simplifier, m, ctx->get_params(), *ctx->m_fmls);
            s = then_s;
            ctx->m_simplifier = s;
            init_preprocess(m, ctx->get_params(), *then_s, *ctx->m_fmls);
        }
        

        dependent_expr_state& fmls = *ctx->m_fmls.get();
        // extract assertions from ctx.
        // it is possible to track proof objects here if wanted.
        // feed them to the simplifier
        ptr_vector<expr> assertions;
        expr_ref_vector units(m);
        ctx->get_assertions(assertions);
        ctx->get_units(units);
        for (expr* e : assertions) 
            fmls.add(dependent_expr(m, e, nullptr, nullptr));
        for (expr* e : units) 
            fmls.add(dependent_expr(m, e, nullptr, nullptr));

        // run in-processing on the assertions
        s->reduce();
        
        scoped_ptr<context> new_ctx = alloc(context, m, m_smt_params, p.ctx.get_params());
        // extract simplified assertions from the simplifier
        // create a new context with the simplified assertions
        // update ctx with the new context.
        for (unsigned i = 0; i < fmls.qtail(); ++i) {
            auto const& de = fmls[i];
            new_ctx->assert_expr(de.fml());
        }
        ctx = new_ctx.detach();

        ctx->internalize_assertions();

        auto old_atoms = m_num_initial_atoms;
        m_num_shared_units = ctx->assigned_literals().size();
        m_num_initial_atoms = ctx->get_num_bool_vars();


        LOG_WORKER(1, " inprocess " << old_atoms << " -> " << m_num_initial_atoms << "\n");
        // TODO: copy user-propagators similar to context::copy.
    }

    void parallel2::worker::collect_statistics(::statistics& st) const {
        ctx->collect_statistics(st);
    }

    void parallel2::worker::cancel() {
        LOG_WORKER(1, " canceling\n");
        m.limit().cancel();
    }

    void parallel2::batch_manager::backtrack(ast_translation& l2g, expr_ref_vector const& core, 
                                             search_tree::node<cube_config>* node) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager backtracking.\n");
        if (m_state != state::is_running)
            return;
        vector<cube_config::literal> g_core;
        for (auto c : core) {
            expr_ref g_c(l2g(c), m);
            if (is_assumption(g_c))
                continue;
            g_core.push_back(expr_ref(l2g(c), m));
        }
        m_search_tree.backtrack(node, g_core);

        IF_VERBOSE(1, m_search_tree.display(verbose_stream() << bounded_pp_exprs(core) << "\n"););
        if (m_search_tree.is_closed()) {
            m_state = state::is_unsat;
            cancel_workers();
        }
    }

    void parallel2::batch_manager::split(ast_translation& l2g, unsigned source_worker_id, 
                                        search_tree::node<cube_config>* node, expr* atom) {
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
        cv.notify_all();
    }

    void parallel2::batch_manager::collect_clause(ast_translation& l2g, unsigned source_worker_id, expr* clause) {
        std::scoped_lock lock(mux);
        expr* g_clause = l2g(clause);
        if (!shared_clause_set.contains(g_clause)) {
            shared_clause_set.insert(g_clause);
            shared_clause sc{source_worker_id, expr_ref(g_clause, m)};
            shared_clause_trail.push_back(sc);
        }
    }

    void parallel2::worker::collect_shared_clauses(ast_translation& g2l) { 
        expr_ref_vector new_clauses = b.return_shared_clauses(g2l, m_shared_clause_limit, id); 
        // iterate over new clauses and assert them in the local context
        for (expr* e : new_clauses) {
            expr_ref local_clause(e, g2l.to());
            ctx->assert_expr(local_clause); 
            LOG_WORKER(2, " asserting shared clause: " << mk_bounded_pp(local_clause, m, 3) << "\n");
        }
    }

    expr_ref_vector parallel2::batch_manager::return_shared_clauses(ast_translation& g2l, unsigned& worker_limit, unsigned worker_id) {
        std::scoped_lock lock(mux);
        expr_ref_vector result(g2l.to());
        for (unsigned i = worker_limit; i < shared_clause_trail.size(); ++i) {
            if (shared_clause_trail[i].source_worker_id == worker_id)
                continue; // skip clauses from the requesting worker
            result.push_back(g2l(shared_clause_trail[i].clause.get()));
        }
        worker_limit = shared_clause_trail.size(); // update the worker limit to the end of the current trail
        return result;
    }

    lbool parallel2::worker::check_cube(expr_ref_vector const& cube) {
        for (auto& atom : cube) 
            asms.push_back(atom);                
        lbool r = l_undef;

        ctx->get_fparams().m_max_conflicts = std::min(m_config.m_threads_max_conflicts, m_config.m_max_conflicts);
        IF_VERBOSE(1, verbose_stream() << " Checking cube\n" << bounded_pp_exprs(cube) << "with max_conflicts: " << ctx->get_fparams().m_max_conflicts << "\n";);
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
        asms.shrink(asms.size() - cube.size());
        LOG_WORKER(1, " DONE checking cube " << r << "\n";);
        return r;
    }

    expr_ref parallel2::worker::get_split_atom() {
        expr_ref result(m);
        double score = 0;
        unsigned n = 0;
        ctx->pop_to_search_lvl();
        for (bool_var v = 0; v < ctx->get_num_bool_vars(); ++v) {
            if (ctx->get_assignment(v) != l_undef)
                continue;
            expr* e = ctx->bool_var2expr(v);
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

    void parallel2::batch_manager::set_sat(ast_translation& l2g, model& m) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager setting SAT.\n");
        if (m_state != state::is_running)
            return;
        m_state = state::is_sat;
        p.ctx.set_model(m.translate(l2g));
        cancel_workers();
    }

    void parallel2::batch_manager::set_unsat(ast_translation& l2g, expr_ref_vector const& unsat_core) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager setting UNSAT.\n");
        if (m_state != state::is_running)
            return;
        m_state = state::is_unsat;    

        // each call to check_sat needs to have a fresh unsat core
        SASSERT(p.ctx.m_unsat_core.empty());
        for (expr* e : unsat_core)
            p.ctx.m_unsat_core.push_back(l2g(e));
        cancel_workers();
    }

    void parallel2::batch_manager::set_exception(unsigned error_code) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager setting exception code: " << error_code << ".\n");
        if (m_state != state::is_running)
            return;
        m_state = state::is_exception_code;
        m_exception_code = error_code;
        cancel_workers();
    }

    void parallel2::batch_manager::set_exception(std::string const& msg) {
        std::scoped_lock lock(mux);
        IF_VERBOSE(1, verbose_stream() << "Batch manager setting exception msg: " << msg << ".\n");
        if (m_state != state::is_running)
            return;
        m_state = state::is_exception_msg;
        m_exception_msg = msg;
        cancel_workers();
    }

    void parallel2::batch_manager::report_assumption_used(ast_translation& l2g, expr* assumption) {
        std::scoped_lock lock(mux);
        p.m_assumptions_used.insert(l2g(assumption));
    }

    lbool parallel2::batch_manager::get_result() const {
        if (m.limit().is_canceled())
            return l_undef; // the main context was cancelled, so we return undef.
        switch (m_state) {
            case state::is_running: // batch manager is still running, but all threads have processed their cubes, which means all cubes were unsat
                if (!m_search_tree.is_closed())
                    throw default_exception("inconsistent end state");
                if (!p.m_assumptions_used.empty()) {
                    // collect unsat core from assumptions used, if any --> case when all cubes were unsat, but depend on nonempty asms, so we need to add these asms to final unsat core
                    SASSERT(p.ctx.m_unsat_core.empty());
                    for (auto a : p.m_assumptions_used)
                        p.ctx.m_unsat_core.push_back(a);
                }
                return l_false;
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

    bool parallel2::batch_manager::get_cube(ast_translation& g2l, unsigned id, expr_ref_vector& cube, node*& n) {
        cube.reset();
        std::unique_lock<std::mutex> lock(mux);
        node* t = nullptr;
        while ((t = m_search_tree.activate_node(n)) == nullptr) {
            // if all threads have reported they are done, then return false
            // otherwise wait for condition variable
            if (m_search_tree.is_closed()) {
                IF_VERBOSE(1, verbose_stream() << "all done\n";);
                cv.notify_all();
                return false;
            }
            if (m_state != state::is_running) {
                IF_VERBOSE(1, verbose_stream() << "aborting get_cube\n";);
                cv.notify_all();
                return false;
            }
            t = m_search_tree.find_active_node();
            if (t) {
                IF_VERBOSE(1, verbose_stream() << "found active node\n";);
                break;
            }
            IF_VERBOSE(1, verbose_stream() << "waiting... " << id << "\n";);
            cv.wait(lock);
            IF_VERBOSE(1, verbose_stream() << "release... " << id << "\n";);
        }
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
        //        IF_VERBOSE(1, verbose_stream() << "got cube " << cube << " from " << " " << t->get_status() << "\n";);
        return true;
    }


    void parallel2::batch_manager::initialize() {
        m_state = state::is_running; 
        m_search_tree.reset();
        smt_parallel_params sp(p.ctx.m_params);
        m_config.m_max_cube_depth = sp.max_cube_depth();
        m_config.m_frugal_cube_only = sp.frugal_cube_only();
        m_config.m_never_cube = sp.never_cube();
        m_config.m_depth_splitting_only = sp.depth_splitting_only();
        m_config.m_iterative_deepening = sp.iterative_deepening();
        m_config.m_beam_search = sp.beam_search();
        m_config.m_cubetree = sp.cubetree();
    }

    void parallel2::batch_manager::collect_statistics(::statistics& st) const {
        st.update("parallel-num_cubes", m_stats.m_num_cubes);
        st.update("parallel-max-cube-size", m_stats.m_max_cube_depth);
    }

    lbool parallel2::operator()(expr_ref_vector const& asms) {
        ast_manager& m = ctx.m;

        if (m.has_trace_stream())
            throw default_exception("trace streams have to be off in parallel mode");
        
        struct scoped_clear {
            parallel2& p;
            scoped_clear(parallel2& p) : p(p) {}
            ~scoped_clear() { p.m_workers.reset(); p.m_assumptions_used.reset(); }
        };
        scoped_clear clear(*this);

        {
            m_batch_manager.initialize();
            m_workers.reset();
            scoped_limits sl(m.limit());
            flet<unsigned> _nt(ctx.m_fparams.m_threads, 1);
            SASSERT(num_threads > 1);
            for (unsigned i = 0; i < num_threads; ++i)
                m_workers.push_back(alloc(worker, i, *this, asms)); // i.e. "new worker(i, *this, asms)"
                
            for (auto w : m_workers)
                sl.push_child(&(w->limit()));

            // Launch threads
            vector<std::thread> threads(num_threads);
            for (unsigned i = 0; i < num_threads; ++i) {
                threads[i] = std::thread([&, i]() {
                    m_workers[i]->run();
                });
            }

            // Wait for all threads to finish
            for (auto& th : threads)
                th.join();

            for (auto w : m_workers)
                w->collect_statistics(ctx.m_aux_stats);     
            m_batch_manager.collect_statistics(ctx.m_aux_stats);
        }

        return m_batch_manager.get_result(); 
    }

}
#endif
