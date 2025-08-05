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
#include "smt/smt_parallel.h"
#include "smt/smt_lookahead.h"

#ifdef SINGLE_THREAD

namespace smt {
    
    lbool parallel::operator()(expr_ref_vector const& asms) {
        return l_undef;
    }
}

#else

#include <thread>
#include <cassert>

namespace smt {

    void parallel::worker::run() {
        ast_translation tr(ctx->m, m);
        while (m.inc()) {
            vector<expr_ref_vector> cubes;
            b.get_cubes(tr, cubes);
            if (cubes.empty())
                return;
            for (auto& cube : cubes) {
                if (!m.inc())
                    return; // stop if the main context is cancelled                
                switch (check_cube(cube)) {
                case l_undef:
                    // return unprocessed cubes to the batch manager
                    // add a split literal to the batch manager.
                    // optionally process other cubes and delay sending back unprocessed cubes to batch manager.
                    b.m_cubes.push_back(cube); // TODO: add access funcs for m_cubes
                    break;
                case l_true: {
                    model_ref mdl;
                    ctx->get_model(mdl);
                    if (mdl) 
                        ctx->set_model(mdl->translate(tr));
                    //b.set_sat(tr, *mdl);
                    return;
                }
                case l_false:
                    // if unsat core only contains assumptions, then unsat
                    // otherwise, extract lemmas that can be shared (units (and unsat core?)).
                    // share with batch manager.
                    // process next cube.
                    ctx->m_unsat_core.reset();
                    for (expr* e : pctx.unsat_core()) // TODO: move this logic to the batch manager since this is per-thread
                        ctx->m_unsat_core.push_back(tr(e));
                    break;
                }
            }
        }
    }

    parallel::worker::worker(parallel& p, context& _ctx, expr_ref_vector const& _asms): p(p), b(p.m_batch_manager), m_smt_params(_ctx.get_fparams()), asms(m) {
        ast_translation g2l(_ctx.m, m);
        for (auto e : _asms) 
            asms.push_back(g2l(e));        
        m_smt_params.m_preprocess = false;
        ctx = alloc(context, m, m_smt_params, _ctx.get_params());
    }


    lbool parallel::worker::check_cube(expr_ref_vector const& cube) {
        for (auto& atom : cube) {
            asms.push_back(atom);
        }
        lbool r = ctx->check(asms.size(), asms.data());
        asms.shrink(asms.size() - cube.size());
        return r;
    }

    void parallel::batch_manager::get_cubes(ast_translation& g2l, vector<expr_ref_vector>& cubes) {
        std::scoped_lock lock(mux);
        if (m_cubes.size() == 1 && m_cubes[0].size() == 0) {
            // special initialization: the first cube is emtpy, have the worker work on an empty cube.
            cubes.push_back(expr_ref_vector(g2l.to()));
            return;
        }

        for (unsigned i = 0; i < std::min(m_max_batch_size / p.num_threads, (unsigned)m_cubes.size()) && !m_cubes.empty(); ++i) {
            auto& cube = m_cubes.back();
            expr_ref_vector l_cube(g2l.to());
            for (auto& e : cube) {
                l_cube.push_back(g2l(e));
            }
            cubes.push_back(l_cube);
            m_cubes.pop_back();
        }
    }

    void parallel::batch_manager::set_sat(ast_translation& l2g, model& m) {
        std::scoped_lock lock(mux);
        if (m_result == l_true || m_result == l_undef) {
            m_result = l_true;
            return;
        }
        m_result = l_true;
        for (auto& c : m_cubes) {
            expr_ref_vector g_cube(l2g.to());
            for (auto& e : c) {
                g_cube.push_back(l2g(e));
            }
            share_lemma(l2g, mk_and(g_cube));
        }
    }
    
    void parallel::batch_manager::return_cubes(ast_translation& l2g, vector<expr_ref_vector>const& cubes, expr_ref_vector const& split_atoms) {
        std::scoped_lock lock(mux);
        for (auto & c : cubes) {
            expr_ref_vector g_cube(l2g.to());
            for (auto& e : c) {
                g_cube.push_back(l2g(e));
            }
            // TODO: split this g_cube on m_split_atoms that are not already in g_cube as literals.
            m_cubes.push_back(g_cube);
        }

        // TODO: avoid making m_cubes too large.
        for (auto& atom : split_atoms) {
            expr_ref g_atom(l2g.from());
            g_atom = l2g(atom);
            if (m_split_atoms.contains(g_atom))
                continue;
            m_split_atoms.push_back(g_atom);
            unsigned sz = m_cubes.size();
            for (unsigned i = 0; i < sz; ++i) {
                m_cubes.push_back(m_cubes[i]); // copy the existing cubes
                m_cubes.back().push_back(m.mk_not(g_atom)); // add the negation of the split atom to each cube
                m_cubes[i].push_back(g_atom);
            }
        }
    }

    expr_ref_vector parallel::worker::get_split_atoms() {
        unsigned k = 1;

        auto candidates = ctx->m_pq_scores.get_heap();
        std::sort(candidates.begin(), candidates.end(),
                [](const auto& a, const auto& b) { return a.priority > b.priority; });

        expr_ref_vector top_lits(m);
        for (const auto& node : candidates) {
            if (ctx->get_assignment(node.key) != l_undef) continue;

            expr* e = ctx->bool_var2expr(node.key);
            if (!e) continue;

            top_lits.push_back(expr_ref(e, m));
            if (top_lits.size() >= k) break;
        }
        return top_lits;
    }

    lbool parallel::new_check(expr_ref_vector const& asms) {
        ast_manager& m = ctx.m;
        {
            scoped_limits sl(m.limit());
            unsigned num_threads = std::min((unsigned)std::thread::hardware_concurrency(), ctx.get_fparams().m_threads);
            SASSERT(num_threads > 1);
            for (unsigned i = 0; i < num_threads; ++i)
                m_workers.push_back(alloc(worker, *this, ctx, asms));
                
            // THIS WILL ALLOW YOU TO CANCEL ALL THE CHILD THREADS
            // within the lexical scope of the code block, creates a data structure that allows you to push children
            // objects to the limit object, so if someone cancels the parent object, the cancellation propagates to the children
            // and that cancellation has the lifetime of the scope
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
        }
        m_workers.clear();
        return m_batch_manager.get_result();        
    }
    
    lbool parallel::operator()(expr_ref_vector const& asms) {

        lbool result = l_undef;
        unsigned num_threads = std::min((unsigned) std::thread::hardware_concurrency(), ctx.get_fparams().m_threads);
        flet<unsigned> _nt(ctx.m_fparams.m_threads, 1);
        unsigned thread_max_conflicts = ctx.get_fparams().m_threads_max_conflicts;
        unsigned max_conflicts = ctx.get_fparams().m_max_conflicts;

        // try first sequential with a low conflict budget to make super easy problems cheap
        // GET RID OF THIS, AND IMMEDIATELY SEND TO THE MULTITHREADED CHECKER
        // THE FIRST BATCH OF CUBES IS EMPTY, AND WE WILL SET ALL THREADS TO WORK ON THE ORIGINAL FORMULA 

        enum par_exception_kind {
            DEFAULT_EX,
            ERROR_EX
        };

        //  MOVE ALL OF THIS INSIDE THE WORKER THREAD AND CREATE/MANAGE LOCALLY
        // SO THEN WE REMOVE THE ENCAPSULATING scoped_ptr_vector ETC, SMT_PARAMS BECOMES SMT_
        vector<smt_params> smt_params;
        scoped_ptr_vector<ast_manager> pms;
        scoped_ptr_vector<context> pctxs;
        vector<expr_ref_vector> pasms;

        ast_manager& m = ctx.m;
        scoped_limits sl(m.limit());
        unsigned finished_id = UINT_MAX;
        std::string        ex_msg;
        par_exception_kind ex_kind = DEFAULT_EX;
        unsigned error_code = 0;
        bool done = false;
        unsigned num_rounds = 0;
        if (m.has_trace_stream())
            throw default_exception("trace streams have to be off in parallel mode");

        
        params_ref params = ctx.get_params();
        for (unsigned i = 0; i < num_threads; ++i) {
            smt_params.push_back(ctx.get_fparams());
            smt_params.back().m_preprocess = false;
        }
                    
        for (unsigned i = 0; i < num_threads; ++i) {
            ast_manager* new_m = alloc(ast_manager, m, true);
            pms.push_back(new_m);
            pctxs.push_back(alloc(context, *new_m, smt_params[i], params)); 
            context& new_ctx = *pctxs.back();
            context::copy(ctx, new_ctx, true);
            new_ctx.set_random_seed(i + ctx.get_fparams().m_random_seed);
            ast_translation tr(m, *new_m);
            pasms.push_back(tr(asms));
            sl.push_child(&(new_m->limit()));
        }

        obj_hashtable<expr> unit_set;
        expr_ref_vector unit_trail(ctx.m);
        unsigned_vector unit_lim;
        for (unsigned i = 0; i < num_threads; ++i) unit_lim.push_back(0);

        std::function<void(void)> collect_units = [&,this]() {
            //return; -- has overhead
            for (unsigned i = 0; i < num_threads; ++i) {
                context& pctx = *pctxs[i];
                pctx.pop_to_base_lvl();
                ast_translation tr(pctx.m, ctx.m);
                unsigned sz = pctx.assigned_literals().size();
                for (unsigned j = unit_lim[i]; j < sz; ++j) {
                    literal lit = pctx.assigned_literals()[j];
                    //IF_VERBOSE(0, verbose_stream() << "(smt.thread " << i << " :unit " << lit << " " << pctx.is_relevant(lit.var()) << ")\n";);
                    if (!pctx.is_relevant(lit.var()))
                        continue;
                    expr_ref e(pctx.bool_var2expr(lit.var()), pctx.m);
                    if (lit.sign()) e = pctx.m.mk_not(e);
                    expr_ref ce(tr(e.get()), ctx.m);
                    if (!unit_set.contains(ce)) {
                        unit_set.insert(ce);
                        unit_trail.push_back(ce);
                    }
                }
            }

            unsigned sz = unit_trail.size();
            for (unsigned i = 0; i < num_threads; ++i) {
                context& pctx = *pctxs[i];
                ast_translation tr(ctx.m, pctx.m);
                for (unsigned j = unit_lim[i]; j < sz; ++j) {
                    expr_ref src(ctx.m), dst(pctx.m);
                    dst = tr(unit_trail.get(j));
                    pctx.assert_expr(dst); // Assert that the conjunction of the assumptions in this unsat core is not satisfiable — prune it from future search
                }
                unit_lim[i] = pctx.assigned_literals().size();
            }
            IF_VERBOSE(1, verbose_stream() << "(smt.thread :units " << sz << ")\n");
        };

        // Gather statistics from all solver contexts
        for (context* c : pctxs) {
            c->collect_statistics(ctx.m_aux_stats);
        }

        // If no thread finished successfully, throw recorded error
        if (finished_id == UINT_MAX) {
            switch (ex_kind) {
            case ERROR_EX: throw z3_error(error_code);
            default: throw default_exception(std::move(ex_msg));
            }
        }
        
    }

}
#endif
