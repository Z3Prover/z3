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
        ast_translation g2l(ctx->m, m);
        ast_translation l2g(m, ctx->m);
        while (m.inc()) {
            vector<expr_ref_vector> cubes;
            b.get_cubes(g2l, cubes);
            if (cubes.empty())
                return;
            for (auto& cube : cubes) {
                if (!m.inc())
                    return; // stop if the main context (i.e. parent thread) is cancelled                
                switch (check_cube(cube)) {
                    case l_undef: {
                        // return unprocessed cubes to the batch manager
                        // add a split literal to the batch manager.
                        // optionally process other cubes and delay sending back unprocessed cubes to batch manager.
                        vector<expr_ref_vector> returned_cubes;
                        returned_cubes.push_back(cube);
                        auto split_atoms = get_split_atoms();
                        b.return_cubes(l2g, returned_cubes, split_atoms);
                        break;
                    }
                    case l_true: {
                        std::cout << "Worker " << id << " found sat cube: " << mk_pp(mk_and(cube), m) << "\n";
                        model_ref mdl;
                        ctx->get_model(mdl);
                        b.set_sat(l2g, *mdl);
                        return;
                    }
                    case l_false: {
                        // if unsat core only contains (external) assumptions (i.e. all the unsat core are asms), then unsat and return as this does NOT depend on cubes
                        // otherwise, extract lemmas that can be shared (units (and unsat core?)).
                        // share with batch manager.
                        // process next cube.
                        expr_ref_vector const& unsat_core = ctx->unsat_core();
                        // If the unsat core only contains assumptions, 
                        // unsatisfiability does not depend on the current cube and the entire problem is unsat.
                        if (all_of(unsat_core, [&](expr* e) { return asms.contains(e); })) {
                            std::cout << "Worker " << id << " determined formula unsat";
                            b.set_unsat(l2g, unsat_core);
                            return;
                        }
                        // TODO: can share lemmas here, such as new units and not(and(unsat_core)), binary clauses, etc.
                        // TODO: remember assumptions used in core so that they get used for the final core.
                        std::cout << "Worker " << id << " found unsat cube: " << mk_pp(mk_and(cube), m) << "\n";
                        b.share_lemma(l2g, mk_not(mk_and(unsat_core)));
                        // share_units();
                        break;
                    }
                }
            }
        }
    }

    parallel::worker::worker(unsigned id, parallel& p, expr_ref_vector const& _asms): id(id), p(p), b(p.m_batch_manager), m_smt_params(p.ctx.get_fparams()), asms(m) {
        ast_translation g2l(p.ctx.m, m);
        for (auto e : _asms) 
            asms.push_back(g2l(e));        
        m_smt_params.m_preprocess = false;
        ctx = alloc(context, m, m_smt_params, p.ctx.get_params());
        context::copy(p.ctx, *ctx, true);
        ctx->set_random_seed(id + m_smt_params.m_random_seed);
    }

    void parallel::worker::share_units() {
        //     obj_hashtable<expr> unit_set;
    //     expr_ref_vector unit_trail(ctx.m);
    //     unsigned_vector unit_lim;
    //     for (unsigned i = 0; i < num_threads; ++i) unit_lim.push_back(0);

    //     // we just want to share lemmas and have a way of remembering how they are shared -- this is the next step
    //     // (this needs to be reworked)
    //     std::function<void(void)> collect_units = [&,this]() {
    //         //return; -- has overhead
    //         for (unsigned i = 0; i < num_threads; ++i) {
    //             context& pctx = *pctxs[i];
    //             pctx.pop_to_base_lvl();
    //             ast_translation tr(pctx.m, ctx.m);
    //             unsigned sz = pctx.assigned_literals().size();
    //             for (unsigned j = unit_lim[i]; j < sz; ++j) {
    //                 literal lit = pctx.assigned_literals()[j];
    //                 //IF_VERBOSE(0, verbose_stream() << "(smt.thread " << i << " :unit " << lit << " " << pctx.is_relevant(lit.var()) << ")\n";);
    //                 if (!pctx.is_relevant(lit.var()))
    //                     continue;
    //                 expr_ref e(pctx.bool_var2expr(lit.var()), pctx.m);
    //                 if (lit.sign()) e = pctx.m.mk_not(e);
    //                 expr_ref ce(tr(e.get()), ctx.m);
    //                 if (!unit_set.contains(ce)) {
    //                     unit_set.insert(ce);
    //                     unit_trail.push_back(ce);
    //                 }
    //             }
    //         }

    //         unsigned sz = unit_trail.size();
    //         for (unsigned i = 0; i < num_threads; ++i) {
    //             context& pctx = *pctxs[i];
    //             ast_translation tr(ctx.m, pctx.m);
    //             for (unsigned j = unit_lim[i]; j < sz; ++j) {
    //                 expr_ref src(ctx.m), dst(pctx.m);
    //                 dst = tr(unit_trail.get(j));
    //                 pctx.assert_expr(dst); // Assert that the conjunction of the assumptions in this unsat core is not satisfiable — prune it from future search
    //             }
    //             unit_lim[i] = pctx.assigned_literals().size();
    //         }
    //         IF_VERBOSE(1, verbose_stream() << "(smt.thread :units " << sz << ")\n");
    //     };
    }

    void parallel::batch_manager::share_lemma(ast_translation& l2g, expr* lemma) {
        std::scoped_lock lock(mux);
        expr_ref g_lemma(l2g(lemma), l2g.to());
        p.ctx.assert_expr(g_lemma); // QUESTION: where does this get shared with the local thread contexts? -- doesn't right now, we will build the scaffolding for this later!  
    }


    // PUT THE LOGIC FOR LEARNING FROM UNSAT CORE HERE IF THE CUBE INTERSECTS WITH IT!!!
    // THERE IS AN EDGE CASE: IF ALL THE CUBES ARE UNSAT, BUT DEPEND ON NONEMPTY ASSUMPTIONS, NEED TO TAKE THE UNION OF THESE ASMS WHEN LEARNING FROM UNSAT CORE
    // DON'T CODE THIS CASE YET: WE ARE JUST TESTING WITH EMPTY ASMS FOR NOW (I.E. WE ARE NOT PASSING IN ASMS). THIS DOES NOT APPLY TO THE INTERNAL "LEARNED" UNSAT CORE
    lbool parallel::worker::check_cube(expr_ref_vector const& cube) {
        for (auto& atom : cube) 
            asms.push_back(atom);                
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
        if (l_true == m_result)
            return;
        m_result = l_true;
        p.ctx.set_model(m.translate(l2g));
        cancel_workers();
    }

    void parallel::batch_manager::set_unsat(ast_translation& l2g, expr_ref_vector const& unsat_core) {
        std::scoped_lock lock(mux);
        if (l_false == m_result)
            return;
        m_result = l_false;       
        p.ctx.m_unsat_core.reset();
        for (expr* e : unsat_core)
            p.ctx.m_unsat_core.push_back(l2g(e));
        cancel_workers();
    }

    void parallel::batch_manager::set_exception(unsigned error_code) {
        std::scoped_lock lock(mux);
        if (m_exception_kind != NO_EX)
            return; // already set
        m_exception_kind = ERROR_CODE_EX;
        m_exception_code = error_code;
        cancel_workers();
    }

    void parallel::batch_manager::set_exception(std::string const& msg) {
        std::scoped_lock lock(mux);
        if (m_exception_kind != NO_EX)
            return; // already set
        m_exception_kind = ERROR_MSG_EX;
        m_exception_msg = msg;
        cancel_workers();
    }

    lbool parallel::batch_manager::get_result() const {
        if (m_exception_kind == ERROR_MSG_EX)
            throw default_exception(m_exception_msg.c_str());
        if (m_exception_kind == ERROR_CODE_EX)
            throw z3_error(m_exception_code);
        if (m.limit().is_canceled())
            return l_undef; // the main context was cancelled, so we return undef.
        return m_result;
    }

#if 0
    for (auto& c : m_cubes) {
        expr_ref_vector g_cube(l2g.to());
        for (auto& e : c) {
            g_cube.push_back(l2g(e));
        }
        share_lemma(l2g, mk_and(g_cube));
    }
#endif
    
// frugal stragety: only split on return cubes
// 
    void parallel::batch_manager::return_cubes(ast_translation& l2g, vector<expr_ref_vector>const& cubes, expr_ref_vector const& split_atoms) {
        std::scoped_lock lock(mux);
        for (auto & c : cubes) {
            expr_ref_vector g_cube(l2g.to());
            for (auto& atom : c) {
                g_cube.push_back(l2g(atom));
            }

            m_cubes.push_back(g_cube); // base cube
            expr_ref_vector& base = m_cubes.back();

            for (auto& atom : m_split_atoms) {
                if (g_cube.contains(atom) || g_cube.contains(m.mk_not(atom)))
                    continue;

                // Split base: one copy with ¬atom, one with atom
                // TODO FIX: THIS CAN RESULT IN SEGFAULT because it's a pointer to a pointer vector, which may have changed!
                m_cubes.push_back(base);                   // push new copy of base cube
                m_cubes.back().push_back(m.mk_not(atom));  // add ¬atom to new copy
                base.push_back(atom);                      // add atom to base cube
            }
        }

        // TODO: avoid making m_cubes too large.
        // QUESTION: do we need to check if any split_atoms are already in the cubes in m_cubes??
        for (auto& atom : split_atoms) {
            expr_ref g_atom(l2g.to());
            g_atom = l2g(atom);
            if (m_split_atoms.contains(g_atom))
                continue;
            m_split_atoms.push_back(g_atom);
            unsigned sz = m_cubes.size();
            for (unsigned i = 0; i < sz; ++i) {
                m_cubes.push_back(m_cubes[i]); // push copy of m_cubes[i]
                m_cubes.back().push_back(m.mk_not(g_atom)); // add ¬p to the copy
                m_cubes[i].push_back(g_atom); // add p to the original
            }
        }
    }

    expr_ref_vector parallel::worker::get_split_atoms() {
        unsigned k = 2;

        auto candidates = ctx->m_pq_scores.get_heap();
        std::sort(candidates.begin(), candidates.end(),
                [](const auto& a, const auto& b) { return a.priority > b.priority; });

        expr_ref_vector top_lits(m);
        for (const auto& node : candidates) {
            if (ctx->get_assignment(node.key) != l_undef) 
                continue;

            expr* e = ctx->bool_var2expr(node.key);
            if (!e) 
                continue;

            top_lits.push_back(expr_ref(e, m));
            if (top_lits.size() >= k) 
                break;
        }
        return top_lits;
    }

    lbool parallel::new_check(expr_ref_vector const& asms) {
        ast_manager& m = ctx.m;

        if (m.has_trace_stream())
            throw default_exception("trace streams have to be off in parallel mode");

        {
            scoped_limits sl(m.limit());
            SASSERT(num_threads > 1);
            for (unsigned i = 0; i < num_threads; ++i)
                m_workers.push_back(alloc(worker, i, *this, asms)); // i.e. "new worker(i, *this, asms)"
                
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

            for (auto w : m_workers) 
                w->collect_statistics(ctx.m_aux_stats);            
        }
        m_workers.clear();
        return m_batch_manager.get_result(); // i.e. all threads have finished all of their cubes -- so if state::is_running is still true, means the entire formula is unsat (otherwise a thread would have returned l_undef)        
    }
    
    lbool parallel::operator()(expr_ref_vector const& asms) {
        std::cout << "Parallel solving with " << asms.size() << " assumptions." << std::endl;
        flet<unsigned> _nt(ctx.m_fparams.m_threads, 1);
        return new_check(asms);
    }

}
#endif
