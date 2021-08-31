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

namespace smt {
    
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

        
        for (unsigned i = 0; i < num_threads; ++i) {
            smt_params.push_back(ctx.get_fparams());
        }
        for (unsigned i = 0; i < num_threads; ++i) {
            ast_manager* new_m = alloc(ast_manager, m, true);
            pms.push_back(new_m);
            pctxs.push_back(alloc(context, *new_m, smt_params[i], ctx.get_params())); 
            context& new_ctx = *pctxs.back();
            context::copy(ctx, new_ctx, true);
            new_ctx.set_random_seed(i + ctx.get_fparams().m_random_seed);
            ast_translation tr(m, *new_m);
            pasms.push_back(tr(asms));
            sl.push_child(&(new_m->limit()));
        }

        auto cube = [](context& ctx, expr_ref_vector& lasms, expr_ref& c) {
            lookahead lh(ctx);
            c = lh.choose();
            if (c) {
                if ((ctx.get_random_value() % 2) == 0) 
                    c = c.get_manager().mk_not(c);
                lasms.push_back(c);
            }
        };

        obj_hashtable<expr> unit_set;
        expr_ref_vector unit_trail(ctx.m);
        unsigned_vector unit_lim;
        for (unsigned i = 0; i < num_threads; ++i) unit_lim.push_back(0);

        std::function<void(void)> collect_units = [&,this]() {
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
                    pctx.assert_expr(dst);
                }
                unit_lim[i] = sz;
            }
            IF_VERBOSE(1, verbose_stream() << "(smt.thread :units " << sz << ")\n");
        };

        std::mutex mux;

        auto worker_thread = [&](int i) {
            try {
                context& pctx = *pctxs[i];
                ast_manager& pm = *pms[i];
                expr_ref_vector lasms(pasms[i]);
                expr_ref c(pm);

                pctx.get_fparams().m_max_conflicts = std::min(thread_max_conflicts, max_conflicts);
                if (num_rounds > 0 && (pctx.get_fparams().m_threads_cube_frequency % num_rounds) == 0) {
                    cube(pctx, lasms, c);
                }
                IF_VERBOSE(1, verbose_stream() << "(smt.thread " << i; 
                           if (num_rounds > 0) verbose_stream() << " :round " << num_rounds;
                           if (c) verbose_stream() << " :cube " << mk_bounded_pp(c, pm, 3);
                           verbose_stream() << ")\n";);
                lbool r = pctx.check(lasms.size(), lasms.data());
                
                if (r == l_undef && pctx.m_num_conflicts >= max_conflicts) {
                    // no-op
                }
                else if (r == l_undef && pctx.m_num_conflicts >= thread_max_conflicts) {
                    return;
                }                
                else if (r == l_false && pctx.unsat_core().contains(c)) {
                    IF_VERBOSE(1, verbose_stream() << "(smt.thread " << i << " :learn " << mk_bounded_pp(c, pm, 3) << ")");
                    pctx.assert_expr(mk_not(mk_and(pctx.unsat_core())));
                    return;
                } 
                

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
                    else if (!first) return;
                }

                for (ast_manager* m : pms) {
                    if (m != &pm) m->limit().cancel();
                }

            }
            catch (z3_error & err) {
                if (finished_id == UINT_MAX) {
                    error_code = err.error_code();
                    ex_kind = ERROR_EX;
                    done = true;
                }
            }
            catch (z3_exception & ex) {
                if (finished_id == UINT_MAX) {
                    ex_msg = ex.msg();
                    ex_kind = DEFAULT_EX;
                    done = true;
                }
            }
            catch (...) {
                if (finished_id == UINT_MAX) {
                    ex_msg = "unknown exception";
                    ex_kind = ERROR_EX;
                    done = true;
                }
            }
        };

        // for debugging:  num_threads = 1;

        while (true) {
            vector<std::thread> threads(num_threads);
            for (unsigned i = 0; i < num_threads; ++i) {
                threads[i] = std::thread([&, i]() { worker_thread(i); });
            }
            for (auto & th : threads) {
                th.join();
            }
            if (done) break;

            collect_units();
            ++num_rounds;
            max_conflicts = (max_conflicts < thread_max_conflicts) ? 0 : (max_conflicts - thread_max_conflicts);
            thread_max_conflicts *= 2;            
        }

        for (context* c : pctxs) {
            c->collect_statistics(ctx.m_aux_stats);
        }

        if (finished_id == UINT_MAX) {
            switch (ex_kind) {
            case ERROR_EX: throw z3_error(error_code);
            default: throw default_exception(std::move(ex_msg));
            }
        }        

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
