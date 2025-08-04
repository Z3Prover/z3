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
                    break;
                case l_true: {
                    model_ref mdl;
                    ctx->get_model(mdl);
                    //b.set_sat(tr, *mdl);
                    return;
                }
                case l_false:
                    // if unsat core only contains assumptions, then unsat
                    // otherwise, extract lemmas that can be shared (units (and unsat core?)).
                    // share with batch manager.
                    // process next cube.
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

        return l_undef;
    }

    void parallel::batch_manager::get_cubes(ast_translation& g2l, vector<expr_ref_vector>& cubes) {
        std::scoped_lock lock(mux);
        if (m_cubes.size() == 1 && m_cubes[0].size() == 0) {
            // special initialization: the first cube is emtpy, have the worker work on an empty cube.
            cubes.push_back(expr_ref_vector(g2l.to()));
            return;
        }
        // TODO adjust to number of worker threads runnin.
        // if the size of m_cubes is less than m_max_batch_size/ num_threads, then return fewer cubes.
        for (unsigned i = 0; i < m_max_batch_size && !m_cubes.empty(); ++i) {
            auto& cube = m_cubes.back();
            expr_ref_vector l_cube(g2l.to());
            for (auto& e : cube) {
                l_cube.push_back(g2l(e));
            }
            cubes.push_back(l_cube);
            m_cubes.pop_back();
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


    lbool parallel::new_check(expr_ref_vector const& asms) {

        ast_manager& m = ctx.m;
        {
            scoped_limits sl(m.limit());
            unsigned num_threads = std::min((unsigned)std::thread::hardware_concurrency(), ctx.get_fparams().m_threads);
            SASSERT(num_threads > 1);
            for (unsigned i = 0; i < num_threads; ++i)
                m_workers.push_back(alloc(worker, *this, ctx, asms));
            for (auto w : m_workers)
                sl.push_child(&(w->limit()));

            // Launch threads
            vector<std::thread> threads(num_threads);
            for (unsigned i = 0; i < num_threads; ++i) {
                threads[i] = std::thread([&, i]() {
                    m_workers[i]->run();
                    }
                );
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
        unsigned max_c = std::min(thread_max_conflicts, 40u);
        flet<unsigned> _mc(ctx.get_fparams().m_max_conflicts, max_c);
        result = ctx.check(asms.size(), asms.data());
        if (result != l_undef || ctx.m_num_conflicts < max_c) {
            return result;
        }        

        enum par_exception_kind {
            DEFAULT_EX,
            ERROR_EX
        };

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


        auto cube_pq = [&](context& ctx, expr_ref_vector& lasms, expr_ref& c) {
            unsigned k = 3; // Number of top literals you want

            ast_manager& m = ctx.get_manager();

            // Get the entire fixed-size priority queue (it's not that big)
            auto candidates = ctx.m_pq_scores.get_heap();  // returns vector<node<key, priority>>

            // Sort descending by priority (higher priority first)
            std::sort(candidates.begin(), candidates.end(),
                    [](const auto& a, const auto& b) { return a.priority > b.priority; });

            expr_ref_vector conjuncts(m);
            unsigned count = 0;

            for (const auto& node : candidates) {
                if (ctx.get_assignment(node.key) != l_undef) continue;

                expr* e = ctx.bool_var2expr(node.key);
                if (!e) continue;


                expr_ref lit(e, m);
                conjuncts.push_back(lit);

                if (++count >= k) break;
            }

            c = mk_and(conjuncts);
            lasms.push_back(c);
        };

        auto cube_score = [&](context& ctx, expr_ref_vector& lasms, expr_ref& c) {
            vector<std::pair<expr_ref, double>> candidates;
            unsigned k = 4; // Get top-k scoring literals
            ast_manager& m = ctx.get_manager();

            // Loop over first 100 Boolean vars
            for (bool_var v = 0; v < 100; ++v) {
                if (ctx.get_assignment(v) != l_undef) continue;

                expr* e = ctx.bool_var2expr(v);
                if (!e) continue;

                literal lit(v, false);
                double score = ctx.get_score(lit);
                if (score == 0.0) continue;

                candidates.push_back(std::make_pair(expr_ref(e, m), score));
            }

            // Sort all candidate literals descending by score
            std::sort(candidates.begin(), candidates.end(),
                [](auto& a, auto& b) { return a.second > b.second; });

            // Clear c and build it as conjunction of top-k
            expr_ref_vector conjuncts(m);

            for (unsigned i = 0; i < std::min(k, (unsigned)candidates.size()); ++i) {
                expr_ref lit = candidates[i].first;
                conjuncts.push_back(lit);
            }

            // Build conjunction and store in c
            c = mk_and(conjuncts);

            // Add the single cube formula to lasms (not each literal separately)
            lasms.push_back(c);
        };

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

        std::mutex mux;

        // Lambda defining the work each SMT thread performs
        auto worker_thread = [&](int i, vector<expr_ref_vector>& cube_batch) {
            try {
                // Get thread-specific context and AST manager
                context& pctx = *pctxs[i];
                ast_manager& pm = *pms[i];

                // Initialize local assumptions and cube
                expr_ref_vector lasms(pasms[i]);

                vector<lbool> results;
                for (expr_ref_vector& cube : cube_batch) {
                    expr_ref_vector lasms_copy(lasms);

                    if (&cube.get_manager() != &pm) {
                            std::cerr << "Manager mismatch on cube: " << mk_bounded_pp(mk_and(cube), pm, 3) << "\n";
                            UNREACHABLE(); // or throw
                        }

                    for (expr* cube_lit : cube) {
                        lasms_copy.push_back(expr_ref(cube_lit, pm));
                    }

                    // Set the max conflict limit for this thread
                    pctx.get_fparams().m_max_conflicts = std::min(thread_max_conflicts, max_conflicts);

                    // Optional verbose logging
                    IF_VERBOSE(1, verbose_stream() << "(smt.thread " << i; 
                            if (num_rounds > 0) verbose_stream() << " :round " << num_rounds;
                            verbose_stream() << " :cube " << mk_bounded_pp(mk_and(cube), pm, 3);
                            verbose_stream() << ")\n";);
                    
                    lbool r = pctx.check(lasms_copy.size(), lasms_copy.data());
                    std::cout << "Thread " << i << " finished cube " << mk_bounded_pp(mk_and(cube), pm, 3) << " with result: " << r << "\n";
                    results.push_back(r);
                }

                lbool r = l_false;
                for (lbool res : results) {
                    if (res == l_true) {
                        r = l_true;
                    } else if (res == l_undef) {
                        if (r == l_false)
                            r = l_undef;
                    }
                }

                 auto cube_intersects_core = [&](expr* cube, const expr_ref_vector &core) {
                    expr_ref_vector cube_lits(pctx.m);
                    flatten_and(cube, cube_lits);
                    for (expr* lit : cube_lits)
                        if (core.contains(lit))
                            return true;
                    return false;
                };

                // Handle results based on outcome and conflict count
                if (r == l_undef && pctx.m_num_conflicts >= max_conflicts)
                    ; // no-op, allow loop to continue
                else if (r == l_undef && pctx.m_num_conflicts >= thread_max_conflicts)
                    return; // quit thread early
                // If cube was unsat and it's in the core, learn from it. i.e. a thread can be UNSAT because the cube c contradicted F. In this case learn the negation of the cube ¬c
                // else if (r == l_false) { 
                //     // IF_VERBOSE(1, verbose_stream() << "(smt.thread " << i << " :learn cube batch " << mk_bounded_pp(cube, pm, 3) << ")" << " unsat_core: " << pctx.unsat_core() << ")");
                //     for (expr* cube : cube_batch) { // iterate over each cube in the batch
                //         if (cube_intersects_core(cube, pctx.unsat_core())) {
                //             // IF_VERBOSE(1, verbose_stream() << "(pruning cube: " << mk_bounded_pp(cube, pm, 3) << " given unsat core: " << pctx.unsat_core() << ")");
                //             pctx.assert_expr(mk_not(mk_and(pctx.unsat_core())));
                //         }
                //     }
                // }

                // Begin thread-safe update of shared result state
                bool first = false;
                {
                    std::lock_guard<std::mutex> lock(mux);
                    if (finished_id == UINT_MAX) {
                        finished_id = i;
                        first = true;
                        result = r;
                        done = true;
                    }
                    if (!first && r != l_undef && result == l_undef) {
                        finished_id = i;
                        result = r;                        
                    }
                    else if (!first) return; // nothing new to contribute
                }

                // Cancel limits on other threads now that a result is known
                for (ast_manager* m : pms) {
                    if (m != &pm) m->limit().cancel();
                }
            } catch (z3_error & err) {
                if (finished_id == UINT_MAX) {
                    error_code = err.error_code();
                    ex_kind = ERROR_EX;
                    done = true;
                }
            } catch (z3_exception & ex) {
                if (finished_id == UINT_MAX) {
                    ex_msg = ex.what();
                    ex_kind = DEFAULT_EX;
                    done = true;
                }
            } catch (...) {
                if (finished_id == UINT_MAX) {
                    ex_msg = "unknown exception";
                    ex_kind = ERROR_EX;
                    done = true;
                }
            }
        };

        struct BatchManager {
            std::mutex mtx;
            vector<vector<expr_ref_vector>> batches;
            unsigned batch_idx = 0;
            unsigned batch_size = 1;

            BatchManager(unsigned batch_size) : batch_size(batch_size) {}

            // translate the next SINGLE batch of batch_size cubes to the thread
            vector<expr_ref_vector> get_next_batch(
                ast_manager &main_ctx_m,
                ast_manager &thread_m
            ) {
                std::lock_guard<std::mutex> lock(mtx);
                vector<expr_ref_vector> cube_batch; // ensure bound to thread manager
                if (batch_idx >= batches.size()) return cube_batch;

                vector<expr_ref_vector> next_batch = batches[batch_idx];

                for (const expr_ref_vector& cube : next_batch) {
                    expr_ref_vector translated_cube_lits(thread_m);
                    for (expr* lit : cube) {
                        // Translate each literal to the thread's manager
                        translated_cube_lits.push_back(translate(lit, main_ctx_m, thread_m));
                    }
                    cube_batch.push_back(translated_cube_lits);
                }

                ++batch_idx;

                return cube_batch;
            }

            // returns a list (vector) of cubes, where each cube is an expr_ref_vector of literals
            vector<expr_ref_vector> cube_batch_pq(context& ctx) {
                unsigned k = 1; // generates 2^k cubes in the batch
                ast_manager& m = ctx.get_manager();

                auto candidates = ctx.m_pq_scores.get_heap();
                std::sort(candidates.begin(), candidates.end(),
                        [](const auto& a, const auto& b) { return a.priority > b.priority; });

                expr_ref_vector top_lits(m);
                for (const auto& node : candidates) {
                    if (ctx.get_assignment(node.key) != l_undef) continue;

                    expr* e = ctx.bool_var2expr(node.key);
                    if (!e) continue;

                    top_lits.push_back(expr_ref(e, m));
                    if (top_lits.size() >= k) break;
                }

                // std::cout << "Top lits:\n";
                // for (unsigned j = 0; j < top_lits.size(); ++j) {
                //     std::cout << "  [" << j << "] " << mk_pp(top_lits[j].get(), m) << "\n";
                // }

                unsigned num_lits = top_lits.size();
                unsigned num_cubes = 1 << num_lits; // 2^num_lits combinations

                vector<expr_ref_vector> cube_batch;

                for (unsigned mask = 0; mask < num_cubes; ++mask) {
                    expr_ref_vector cube_lits(m);
                    for (unsigned i = 0; i < num_lits; ++i) {
                        expr_ref lit(top_lits[i].get(), m);
                        if ((mask >> i) & 1)
                            cube_lits.push_back(mk_not(lit));
                        else
                            cube_lits.push_back(lit);
                    }
                    cube_batch.push_back(cube_lits);
                }

                std::cout << "Cubes out:\n";
                for (unsigned j = 0; j < cube_batch.size(); ++j) {
                    std::cout << "  [" << j << "]\n";
                    for (unsigned k = 0; k < cube_batch[j].size(); ++k) {
                        std::cout << "     [" << k << "] " << mk_pp(cube_batch[j][k].get(), m) << "\n";
                    }
                }
                
                return cube_batch;
            };
            
            // returns a vector of new cubes batches. each cube batch is a vector of expr_ref_vector cubes
            vector<vector<expr_ref_vector>> gen_new_batches(context& main_ctx) {
                vector<vector<expr_ref_vector>> cube_batches;

                // Get all cubes in the main context's manager
                vector<expr_ref_vector> all_cubes = cube_batch_pq(main_ctx);

                ast_manager &m = main_ctx.get_manager();

                // Partition into batches
                for (unsigned start = 0; start < all_cubes.size(); start += batch_size) {
                    vector<expr_ref_vector> batch;

                    unsigned end = std::min(start + batch_size, all_cubes.size());
                    for (unsigned j = start; j < end; ++j) {
                        batch.push_back(all_cubes[j]);
                    }

                    cube_batches.push_back(batch);
                }
                batch_idx = 0; // Reset index for next round
                return cube_batches;
            }

            void check_for_new_batches(context& main_ctx) {
                std::lock_guard<std::mutex> lock(mtx);
                if (batch_idx >= batches.size()) {
                    batches = gen_new_batches(main_ctx);
                }
            }
        };
    
        BatchManager batch_manager(1);

        // Thread scheduling loop
        while (true) {
            vector<std::thread> threads(num_threads);
            batch_manager.check_for_new_batches(ctx);

            // Launch threads
            for (unsigned i = 0; i < num_threads; ++i) {
                // [&, i] is the lambda's capture clause: capture all variables by reference (&) except i, which is captured by value.
                threads[i] = std::thread([&, i]() {
                    while (!done) {
                        auto next_batch = batch_manager.get_next_batch(ctx.m, *pms[i]);
                        if (next_batch.empty()) break; // No more work

                        worker_thread(i, next_batch);
                    }
                });
            }

            // Wait for all threads to finish
            for (auto & th : threads) {
                th.join();
            }

            // Stop if one finished with a result
            if (done) break;

            // Otherwise update shared state and retry
            collect_units();
            ++num_rounds;
            max_conflicts = (max_conflicts < thread_max_conflicts) ? 0 : (max_conflicts - thread_max_conflicts);
            thread_max_conflicts *= 2;    
        }

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

        // Handle result: translate model/unsat core back to main context
        model_ref mdl;        
        context& pctx = *pctxs[finished_id];
        ast_translation tr(*pms[finished_id], m);
        switch (result) {
        case l_true: 
            pctx.get_model(mdl);
            if (mdl) 
                ctx.set_model(mdl->translate(tr));            
            break;
        case l_false:
            ctx.m_unsat_core.reset();
            for (expr* e : pctx.unsat_core()) 
                ctx.m_unsat_core.push_back(tr(e));
            break;
        default:
            break;
        }

        return result;
    }

}
#endif
