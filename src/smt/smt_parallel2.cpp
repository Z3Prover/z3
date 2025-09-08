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
#include "smt/smt_parallel2.h"
#include "smt/smt_lookahead.h"
#include "params/smt_parallel_params.hpp"

#include <cmath>

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


#define LOG_WORKER(lvl, s) IF_VERBOSE(lvl, verbose_stream() << "Worker " << id << s)

namespace smt {

 

    void parallel2::worker::run() {
        search_tree::node<cube_config>* node = nullptr;
        expr_ref_vector cube(m);
        while (true) { 
            collect_shared_clauses(m_g2l);

            if (!b.get_cube(m_g2l, id, cube, node)) {
                LOG_WORKER(1, " no more cubes\n");
                return;
            }

        check_cube_start:
            LOG_WORKER(1, " CUBE SIZE IN MAIN LOOP: " << cube.size() << "\n");
            lbool r = check_cube(cube);

            if (!m.inc()) {
                b.set_exception("context cancelled");
                return;
            }
            
            switch (r) {
                case l_undef: {
                    LOG_WORKER(1, " found undef cube\n");
                    // return unprocessed cubes to the batch manager
                    // add a split literal to the batch manager.
                    // optionally process other cubes and delay sending back unprocessed cubes to batch manager.
                    auto atom = get_split_atom();
                    if (!atom)
                        goto check_cube_start;
                    b.split(m_l2g, id, node, atom);
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
                    // if unsat core only contains (external) assumptions (i.e. all the unsat core are asms), then unsat and return as this does NOT depend on cubes
                    // otherwise, extract lemmas that can be shared (units (and unsat core?)).
                    // share with batch manager.
                    // process next cube.
                    expr_ref_vector const& unsat_core = ctx->unsat_core();
                    LOG_WORKER(2, " unsat core:\n"; for (auto c : unsat_core) verbose_stream() << mk_bounded_pp(c, m, 3) << "\n");
                    // If the unsat core only contains assumptions, 
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
                    b.backtrack(m_l2g, unsat_core, node);
                    break;
                }
            }    
            if (m_config.m_share_units)
                share_units(m_l2g);
        }
    }

    parallel2::worker::worker(unsigned id, parallel2& p, expr_ref_vector const& _asms): 
        id(id), p(p), b(p.m_batch_manager), m_smt_params(p.ctx.get_fparams()), asms(m),
        m_g2l(p.ctx.m, m),
        m_l2g(m, p.ctx.m) {
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

        IF_VERBOSE(1, m_search_tree.display(verbose_stream() << core << "\n"););
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
        expr_ref_vector new_clauses = b.return_shared_clauses(g2l, m_shared_clause_limit, id); // get new clauses from the batch manager
        // iterate over new clauses and assert them in the local context
        for (expr* e : new_clauses) {
            expr_ref local_clause(e, g2l.to()); // e was already translated to the local context in the batch manager!!
            ctx->assert_expr(local_clause); // assert the clause in the local context
            LOG_WORKER(2, " asserting shared clause: " << mk_bounded_pp(local_clause, m, 3) << "\n");
        }
    }

    // get new clauses from the batch manager and assert them in the local context
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

        ctx->get_fparams().m_max_conflicts = std::min((cube.size() + 1) *m_config.m_threads_max_conflicts, m_config.m_max_conflicts);
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

        for (bool_var v = 0; v < ctx->get_num_bool_vars(); ++v) {
            if (ctx->get_assignment(v) != l_undef)
                continue;
            expr* e = ctx->bool_var2expr(v);
            if (!e)
                continue;

            double new_score = ctx->m_lit_scores[0][v] * ctx->m_lit_scores[1][v];

            // decay the scores
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

        // every time we do a check_sat call, don't want to have old info coming from a prev check_sat call
        // the unsat core gets reset internally in the context after each check_sat, so we assert this property here
        // takeaway: each call to check_sat needs to have a fresh unsat core
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
        //ctx->collect_statistics(st);
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
                
            // THIS WILL ALLOW YOU TO CANCEL ALL THE CHILD THREADS
            // within the lexical scope of the code block, creates a data structure that allows you to push children
            // objects to the limit object, so if someone cancels the parent object, the cancellation propagates to the children
            // and that cancellation has the lifetime of the scope
            // even if this code doesn't expliclty kill the main thread, still applies bc if you e.g. Ctrl+C the main thread, the children threads need to be cancelled
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

        return m_batch_manager.get_result(); // i.e. all threads have finished all of their cubes -- so if state::is_running is still true, means the entire formula is unsat (otherwise a thread would have returned l_undef)        
    }

}
#endif
