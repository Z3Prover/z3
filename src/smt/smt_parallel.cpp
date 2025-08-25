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
#include "params/smt_parallel_params.hpp"

#ifdef SINGLE_THREAD

namespace smt {
    
    lbool parallel::operator()(expr_ref_vector const& asms) {
        return l_undef;
    }
}

#else

#include <thread>
#include <cassert>

#define LOG_WORKER(lvl, s) IF_VERBOSE(lvl, verbose_stream() << "Worker " << id << s)

namespace smt {

    void parallel::worker::run() {
        while (m.inc()) { // inc: increase the limit and check if it is canceled, vs m.limit().is_canceled() is readonly. the .limit() is also not necessary (m.inc() etc provides a convenience wrapper)
            vector<expr_ref_vector> cubes;
            b.get_cubes(m_g2l, cubes);
            if (cubes.empty())
                return;
            collect_shared_clauses(m_g2l);
            for (auto& cube : cubes) {
                if (!m.inc()) {
                    b.set_exception("context cancelled");
                    return;
                }
                LOG_WORKER(1, " checking cube: " << mk_bounded_pp(mk_and(cube), m, 3) << " max-conflicts " << m_config.m_threads_max_conflicts << "\n");
                lbool r = check_cube(cube);
                if (m.limit().is_canceled()) {
                    LOG_WORKER(1, " context cancelled\n");
                    return;           
                }
                switch (r) {
                    case l_undef: {
                        if (m.limit().is_canceled())
                            break;
                        LOG_WORKER(1, " found undef cube\n");
                        // return unprocessed cubes to the batch manager
                        // add a split literal to the batch manager.
                        // optionally process other cubes and delay sending back unprocessed cubes to batch manager.
                        if (!m_config.m_never_cube) {
                            vector<expr_ref_vector> returned_cubes;
                            returned_cubes.push_back(cube);
                            auto split_atoms = get_split_atoms();
                            b.return_cubes(m_l2g, returned_cubes, split_atoms);
                        }
                        update_max_thread_conflicts();
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
                        if (m_config.m_share_conflicts)
                            b.collect_clause(m_l2g, id, mk_not(mk_and(unsat_core)));
                        break;
                    }
                }     
            }
            if (m_config.m_share_units)
                share_units(m_l2g);
        }
    }

    parallel::worker::worker(unsigned id, parallel& p, expr_ref_vector const& _asms): 
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

        // don't share initial units
        ctx->pop_to_base_lvl();
        m_num_shared_units = ctx->assigned_literals().size();

        m_num_initial_atoms = ctx->get_num_bool_vars();
    }

    void parallel::worker::share_units(ast_translation& l2g) {
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

    void parallel::worker::collect_statistics(::statistics& st) const {
        ctx->collect_statistics(st);
    }

    void parallel::worker::cancel() {
        LOG_WORKER(1, " canceling\n");
        m.limit().cancel();
    }

    void parallel::batch_manager::init_parameters_state() {
        auto& smt_params = p.ctx.get_fparams();
        std::function<std::function<void(void)>(unsigned&)> inc = [](unsigned& v) { return [&]() -> void { ++v; }; };
        std::function<std::function<void(void)>(unsigned&)> dec = [](unsigned& v) { return [&]() -> void { if (v > 0) --v; }; };       
        std::function<std::function<void(void)>(bool&)> incb = [](bool& v) { return [&]() -> void { v = true; }; };
        std::function<std::function<void(void)>(bool&)> decb = [](bool& v) { return [&]() -> void { v = false; }; };
        std::function<parameter_state(unsigned&)> unsigned_parameter = [&](unsigned& p) -> parameter_state {
            return { { { p , 1.0}},
                       { { 1.0, inc(p) }, { 1.0, dec(p) }} 
                   };
        };
        std::function<parameter_state(bool&)> bool_parameter = [&](bool& p) -> parameter_state {
            return { { { p , 1.0}},
                       { { 1.0, incb(p) }, { 1.0, decb(p) }}
            };
        };

        parameter_state s1 = unsigned_parameter(smt_params.m_arith_branch_cut_ratio);
        parameter_state s2 = bool_parameter(smt_params.m_arith_eager_eq_axioms);    

        //  arith.enable_hnf(bool) (default: true)
        //  arith.greatest_error_pivot(bool) (default: false)
        //  arith.int_eq_branch(bool) (default: false)
        //  arith.min(bool) (default: false)
        //  arith.nl.branching(bool) (default: true)
        //  arith.nl.cross_nested(bool) (default: true)
        //  arith.nl.delay(unsigned int) (default: 10)
        //  arith.nl.expensive_patching(bool) (default: false)
        //  arith.nl.expp(bool) (default: false)
        //  arith.nl.gr_q(unsigned int) (default: 10)
        //  arith.nl.grobner(bool) (default: true)
        //  arith.nl.grobner_cnfl_to_report(unsigned int) (default: 1) };
    }

    void parallel::batch_manager::collect_clause(ast_translation& l2g, unsigned source_worker_id, expr* clause) {
        std::scoped_lock lock(mux);
        expr* g_clause = l2g(clause);
        if (!shared_clause_set.contains(g_clause)) {
            shared_clause_set.insert(g_clause);
            shared_clause sc{source_worker_id, expr_ref(g_clause, m)};
            shared_clause_trail.push_back(sc);
        }
    }

    void parallel::worker::collect_shared_clauses(ast_translation& g2l) { 
        expr_ref_vector new_clauses = b.return_shared_clauses(g2l, m_shared_clause_limit, id); // get new clauses from the batch manager
        // iterate over new clauses and assert them in the local context
        for (expr* e : new_clauses) {
            expr_ref local_clause(e, g2l.to()); // e was already translated to the local context in the batch manager!!
            ctx->assert_expr(local_clause); // assert the clause in the local context
            LOG_WORKER(2, " asserting shared clause: " << mk_bounded_pp(local_clause, m, 3) << "\n");
        }
    }

    // get new clauses from the batch manager and assert them in the local context
    expr_ref_vector parallel::batch_manager::return_shared_clauses(ast_translation& g2l, unsigned& worker_limit, unsigned worker_id) {
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

    lbool parallel::worker::check_cube(expr_ref_vector const& cube) {
        for (auto& atom : cube) 
            asms.push_back(atom);                
        lbool r = l_undef;

        ctx->get_fparams().m_max_conflicts = std::min(m_config.m_threads_max_conflicts, m_config.m_max_conflicts);
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

    void parallel::batch_manager::get_cubes(ast_translation& g2l, vector<expr_ref_vector>& cubes) {
        std::scoped_lock lock(mux);
        if (m_cubes.size() == 1 && m_cubes[0].empty()) {
            // special initialization: the first cube is emtpy, have the worker work on an empty cube.
            cubes.push_back(expr_ref_vector(g2l.to()));
            return;
        }

        for (unsigned i = 0; i < std::min(m_max_batch_size / p.num_threads, (unsigned)m_cubes.size()) && !m_cubes.empty(); ++i) {
            if (m_config.m_frugal_deepest_cube_only) {
                // get the deepest set of cubes
                auto& deepest_cubes = m_cubes_depth_sets.rbegin()->second;
                unsigned idx = rand() % deepest_cubes.size();
                auto& cube = deepest_cubes[idx]; // get a random cube from the deepest set

                expr_ref_vector l_cube(g2l.to());
                for (auto& e : cube) {
                    l_cube.push_back(g2l(e));
                }
                cubes.push_back(l_cube);
                
                deepest_cubes.erase(deepest_cubes.begin() + idx); // remove the cube from the set
                if (deepest_cubes.empty())
                    m_cubes_depth_sets.erase(m_cubes_depth_sets.size() - 1);
            } else {
                auto& cube = m_cubes.back();
                expr_ref_vector l_cube(g2l.to());
                for (auto& e : cube) {
                    l_cube.push_back(g2l(e));
                }
                cubes.push_back(l_cube);
                m_cubes.pop_back();
            }
        }
    }

    void parallel::batch_manager::set_sat(ast_translation& l2g, model& m) {
        std::scoped_lock lock(mux);
        if (m_state != state::is_running)
            return;
        m_state = state::is_sat;
        p.ctx.set_model(m.translate(l2g));
        cancel_workers();
    }

    void parallel::batch_manager::set_unsat(ast_translation& l2g, expr_ref_vector const& unsat_core) {
        std::scoped_lock lock(mux);
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

    void parallel::batch_manager::set_exception(unsigned error_code) {
        std::scoped_lock lock(mux);
        if (m_state != state::is_running)
            return;
        m_state = state::is_exception_code;
        m_exception_code = error_code;
        cancel_workers();
    }

    void parallel::batch_manager::set_exception(std::string const& msg) {
        std::scoped_lock lock(mux);
        if (m_state != state::is_running || m.limit().is_canceled())
            return;
        m_state = state::is_exception_msg;
        m_exception_msg = msg;
        cancel_workers();
    }

    void parallel::batch_manager::report_assumption_used(ast_translation& l2g, expr* assumption) {
        std::scoped_lock lock(mux);
        p.m_assumptions_used.insert(l2g(assumption));
    }

    lbool parallel::batch_manager::get_result() const {
        if (m.limit().is_canceled())
            return l_undef; // the main context was cancelled, so we return undef.
        switch (m_state) {
            case state::is_running: // batch manager is still running, but all threads have processed their cubes, which means all cubes were unsat
                if (!m_cubes.empty() || (m_config.m_frugal_deepest_cube_only && !m_cubes_depth_sets.empty()))
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

    /*
    Batch manager maintains C_batch, A_batch.
    C_batch - set of cubes 
    A_batch - set of split atoms.
    return_cubes is called with C_batch A_batch C A.
    C_worker - one or more cubes
    A_worker - split atoms form the worker thread.
    
    Assumption: A_worker does not occur in C_worker.
    
    ------------------------------------------------------------------------------------------------------------------------------------------------------------
    Greedy strategy:
    For each returned cube c from the worker, you split it on all split atoms not in it (i.e., A_batch \ atoms(c)), plus any new atoms from A_worker.
    For each existing cube in the batch, you also split it on the new atoms from A_worker.
    
    return_cubes C_batch A_batch C_worker A_worker:
            C_batch <- { cube * 2^(A_worker u (A_batch \ atoms(cube)) | cube in C_worker } u
                       { cube * 2^(A_worker \ A_batch) | cube in C_batch }
                    = 
                        let C_batch' = C_batch u { cube * 2^(A_batch \ atoms(cube)) | cube in C_worker }
                        in { cube * 2^(A_worker \ A_batch) | cube in C_batch' }
            A_batch <- A_batch u A_worker
    
    ------------------------------------------------------------------------------------------------------------------------------------------------------------
    Frugal strategy: only split on worker cubes
    
    case 1: thread returns no cubes, just atoms: just create 2^k cubes from all combinations of atoms so far.
    return_cubes C_batch A_batch [[]] A_worker:
            C_batch <- C_batch u 2^(A_worker u A_batch), 
            A_batch <- A_batch u A_worker
    
    case 2: thread returns both cubes and atoms
    Only the returned cubes get split by the newly discovered atoms (A_worker). Existing cubes are not touched.
    return_cubes C_batch A_batch C_worker A_worker:
           C_batch <- C_batch u { cube * 2^A_worker | cube in C_worker }.
           A_batch <- A_batch u A_worker
    
    This means:
    Only the returned cubes get split by the newly discovered atoms (A_worker).
    Existing cubes are not touched.
    
    ------------------------------------------------------------------------------------------------------------------------------------------------------------
    Hybrid: Between Frugal and Greedy: (generalizes the first case of empty cube returned by worker) -- don't focus on this approach
            i.e. Expand only the returned cubes, but allow them to be split on both new and old atoms not already in them.
    
            C_batch <- C_batch u { cube * 2^(A_worker u (A_batch \ atoms(cube)) | cube in C_worker }
            A_batch <- A_batch u A_worker
    
    ------------------------------------------------------------------------------------------------------------------------------------------------------------
    Final thought (do this!): use greedy strategy by a policy when C_batch, A_batch, A_worker are "small". -- want to do this. switch to frugal strategy after reaching size limit
    */

    // currenly, the code just implements the greedy strategy
    void parallel::batch_manager::return_cubes(ast_translation& l2g, vector<expr_ref_vector>const& C_worker, expr_ref_vector const& A_worker) {
        SASSERT(!m_config.never_cube());

        auto atom_in_cube = [&](expr_ref_vector const& cube, expr* atom) {
            return any_of(cube, [&](expr* e) { return e == atom || (m.is_not(e, e) && e == atom); });
        };

        auto add_split_atom = [&](expr* atom, unsigned start) {
            unsigned stop = m_cubes.size();
            for (unsigned i = start; i < stop; ++i) {
                // copy the last cube so that expanding m_cubes doesn't invalidate reference.
                auto cube = m_cubes[i];
                if (cube.size() >= m_config.m_max_cube_size)
                    continue;
                m_cubes.push_back(cube);
                m_cubes.back().push_back(m.mk_not(atom));
                m_cubes[i].push_back(atom);
                m_stats.m_max_cube_size = std::max(m_stats.m_max_cube_size, m_cubes.back().size());
                m_stats.m_num_cubes += 2;
            }
        };

        // apply the frugal strategy to ALL incoming worker cubes, but save in the deepest cube data structure
        auto add_split_atom_deepest_cubes = [&](expr* atom) {
            for (auto& c : C_worker) {
                expr_ref_vector g_cube(l2g.to());
                for (auto& atom : c)
                    g_cube.push_back(l2g(atom));
                if (g_cube.size() >= m_config.m_max_cube_size) // we already added this before!! we just need to add the splits now
                    continue;

                // add depth set d+1 if it doesn't exist yet
                unsigned d = g_cube.size();
                if (m_cubes_depth_sets.find(d + 1) == m_cubes_depth_sets.end())
                    m_cubes_depth_sets[d + 1] = vector<expr_ref_vector>();

                // split on the negative atom
                m_cubes_depth_sets[d + 1].push_back(g_cube);
                m_cubes_depth_sets[d + 1].back().push_back(m.mk_not(atom));
                
                // need to split on the positive atom too
                g_cube.push_back(atom);
                m_cubes_depth_sets[d + 1].push_back(g_cube);

                m_stats.m_num_cubes += 2;
                m_stats.m_max_cube_size = std::max(m_stats.m_max_cube_size, d + 1);
            }
        };

        std::scoped_lock lock(mux);
        unsigned max_greedy_cubes = 1000;
        bool greedy_mode = (m_cubes.size() <= max_greedy_cubes) && !m_config.m_frugal_cube_only && !m_config.m_frugal_deepest_cube_only;
        unsigned a_worker_start_idx = 0;

        //
        // --- Phase 1: Greedy split of *existing* cubes on new A_worker atoms (greedy) ---
        //
        if (greedy_mode) {
            for (; a_worker_start_idx < A_worker.size(); ++a_worker_start_idx) {
                expr_ref g_atom(l2g(A_worker[a_worker_start_idx]), l2g.to());
                if (m_split_atoms.contains(g_atom))
                    continue;
                m_split_atoms.push_back(g_atom);

                add_split_atom(g_atom, 0); // split all *existing* cubes
                if (m_cubes.size() > max_greedy_cubes) {
                    greedy_mode = false;
                    ++a_worker_start_idx; // start frugal from here
                    break;
                }
            }
        }

        unsigned initial_m_cubes_size = m_cubes.size(); // where to start processing the worker cubes after splitting the EXISTING cubes on the new worker atoms

        // --- Phase 2: Process worker cubes (greedy) ---
        for (auto& c : C_worker) {
            expr_ref_vector g_cube(l2g.to());
            for (auto& atom : c)
                g_cube.push_back(l2g(atom));
            unsigned start = m_cubes.size(); // update start after adding each cube so we only process the current cube being added

            if (m_config.m_frugal_deepest_cube_only) {
                // need to add the depth set if it doesn't exist yet
                if (m_cubes_depth_sets.find(g_cube.size()) == m_cubes_depth_sets.end()) {
                    m_cubes_depth_sets[g_cube.size()] = vector<expr_ref_vector>();
                }
                m_cubes_depth_sets[g_cube.size()].push_back(g_cube);
                m_stats.m_num_cubes += 1;
                m_stats.m_max_cube_size = std::max(m_stats.m_max_cube_size, g_cube.size());
            } else {
                m_cubes.push_back(g_cube);
            }

            if (greedy_mode) {
                // Split new cube on all existing m_split_atoms not in it
                for (auto g_atom : m_split_atoms) {
                    if (!atom_in_cube(g_cube, g_atom)) {
                        add_split_atom(g_atom, start);
                        if (m_cubes.size() > max_greedy_cubes) {
                            greedy_mode = false;
                            break;
                        }
                    }
                }
            }
        }

        // --- Phase 3: Frugal fallback: only process NEW worker cubes with NEW atoms ---
        if (!greedy_mode) {
            for (unsigned i = a_worker_start_idx; i < A_worker.size(); ++i) {
                expr_ref g_atom(l2g(A_worker[i]), l2g.to());
                if (!m_split_atoms.contains(g_atom))
                    m_split_atoms.push_back(g_atom);
                if (m_config.m_frugal_deepest_cube_only) {
                    add_split_atom_deepest_cubes(g_atom);
                } else {
                    add_split_atom(g_atom, initial_m_cubes_size);
                }
            }
        }
    }

    expr_ref_vector parallel::worker::get_split_atoms() {
        unsigned k = 2;

        // auto candidates = ctx->m_pq_scores.get_heap();
        auto candidates = ctx->m_lit_scores;
        std::vector<std::pair<double, expr*>> top_k; // will hold at most k elements

        for (bool_var v = 0; v < ctx->get_num_bool_vars(); ++v) {
            if (ctx->get_assignment(v) != l_undef)
                continue;
            expr* e = ctx->bool_var2expr(v);
            if (!e)
                continue;

            double score = ctx->m_lit_scores[0][v] * ctx->m_lit_scores[1][v];

            // decay the scores
            ctx->m_lit_scores[0][v] /= 2;
            ctx->m_lit_scores[1][v] /= 2;

            // insert into top_k. linear scan since k is very small
            if (top_k.size() < k) {
                top_k.push_back({score, e});
            } else {
                // find the smallest in top_k and replace if we found a new min
                size_t min_idx = 0;
                for (size_t i = 1; i < k; ++i)
                    if (top_k[i].first < top_k[min_idx].first)
                        min_idx = i;

                if (score > top_k[min_idx].first) {
                    top_k[min_idx] = {score, e};
                }
            }
        }

        expr_ref_vector top_lits(m);
        for (auto& p : top_k)
            top_lits.push_back(expr_ref(p.second, m));
        
        IF_VERBOSE(3, verbose_stream() << "top literals " << top_lits << " head size " << ctx->m_lit_scores->size() << " num vars " << ctx->get_num_bool_vars() << "\n");
        
        return top_lits;
    }

    void parallel::batch_manager::initialize() {
        m_state = state::is_running;
        m_cubes.reset();
        m_cubes.push_back(expr_ref_vector(m)); // push empty cube
        
        if (m_config.m_frugal_deepest_cube_only) {
            m_cubes_depth_sets.clear();
        }
        
        m_split_atoms.reset();
        smt_parallel_params sp(p.ctx.m_params);
        m_config.m_max_cube_size = sp.max_cube_size();
        m_config.m_frugal_cube_only = sp.frugal_cube_only();
        m_config.m_never_cube = sp.never_cube();
        m_config.m_frugal_deepest_cube_only = sp.frugal_deepest_cube_only();
    }

    void parallel::batch_manager::collect_statistics(::statistics& st) const {
        //ctx->collect_statistics(st);
        st.update("parallel-num_cubes", m_stats.m_num_cubes);
        st.update("parallel-max-cube-size", m_stats.m_max_cube_size);
    }

    lbool parallel::operator()(expr_ref_vector const& asms) {
        ast_manager& m = ctx.m;

        if (m.has_trace_stream())
            throw default_exception("trace streams have to be off in parallel mode");
        
        struct scoped_clear {
            parallel& p;
            scoped_clear(parallel& p) : p(p) {}
            ~scoped_clear() { p.m_workers.clear();  p.m_assumptions_used.reset(); }
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
