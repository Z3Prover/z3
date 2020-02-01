/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_parallel.cpp

Abstract:

    Parallel SMT, portfolio loop specialized to SMT core.

Author:

    nbjorner 2020-01-31

--*/

#include "smt/smt_parallel.h"
#include "util/scoped_ptr_vector.h"

namespace smt {

    void parallel::add_unit(context& pctx, expr* e) {
        std::lock_guard<std::mutex> lock(m_mux);
        ast_translation tr(pctx.m, ctx.m);
        expr_ref u (tr(e), ctx.m);
        if (!m_unit_set.contains(u)) {
            m_unit_trail.push_back(u);
            m_unit_set.insert(u);
        }
    }

    void parallel::get_units(unsigned idx, context& pctx) {
        std::lock_guard<std::mutex> lock(m_mux);
        ast_translation tr(ctx.m, pctx.m);
        for (unsigned i = m_unit_lim[idx]; i < m_unit_trail.size(); ++i) {
            expr_ref u (tr(m_unit_trail.get(i)), pctx.m);
            pctx.assert_expr(u);
        }
    }
    
    lbool parallel::operator()(expr_ref_vector const& asms) {

        enum par_exception_kind {
            DEFAULT_EX,
            ERROR_EX
        };

        ctx.internalize_assertions();
        scoped_ptr_vector<ast_manager> pms;
        scoped_ptr_vector<context> pctxs;
        vector<expr_ref_vector> pasms;
        ast_manager& m = ctx.m;
        lbool result = l_undef;
        unsigned num_threads = ctx.m_fparams.m_threads;
        flet<unsigned> _nt(ctx.m_fparams.m_threads, 1);
        unsigned finished_id = UINT_MAX;
        std::string        ex_msg;
        par_exception_kind ex_kind = DEFAULT_EX;
        unsigned error_code = 0;

        for (unsigned i = 0; i < num_threads; ++i) {
            ast_manager* new_m = alloc(ast_manager, m, true);
            pms.push_back(new_m);
            pctxs.push_back(alloc(context, *new_m, ctx.get_fparams(), ctx.get_params())); 
            context& new_ctx = *pctxs.back();
            context::copy(ctx, new_ctx);
            new_ctx.set_random_seed(i + ctx.get_fparams().m_random_seed);
            ast_translation tr(*new_m, m);
            pasms.push_back(tr(asms));
            m_unit_lim.push_back(0);
            new_ctx.set_par(i, this);
        }

        std::mutex mux;
        auto worker_thread = [&](int i) {
            try {
                IF_VERBOSE(0, verbose_stream() << "thread " << i << "\n";);
                context& pctx = *pctxs[i];
                ast_manager& pm = *pms[i];

                lbool r = pctx.check(pasms[i].size(), pasms[i].c_ptr());
                bool first = false;
                {
                    std::lock_guard<std::mutex> lock(mux);
                    if (finished_id == UINT_MAX) {
                        finished_id = i;
                        first = true;
                        result = r;
                    }
                }
                if (!first) return;

                for (ast_manager* m : pms) {
                    if (m != &pm) m->limit().cancel();
                }

            }
            catch (z3_error & err) {
                error_code = err.error_code();
                ex_kind = ERROR_EX;                
            }
            catch (z3_exception & ex) {
                ex_msg = ex.msg();
                ex_kind = DEFAULT_EX;    
            }
        };

        vector<std::thread> threads(num_threads);
        for (unsigned i = 0; i < num_threads; ++i) {
            threads[i] = std::thread([&, i]() { worker_thread(i); });
        }
        for (auto & th : threads) {
            th.join();
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
            if (mdl) {
                ctx.m_model = mdl->translate(tr);
            }
            break;
        case l_false:
            for (expr* e : pctx.m_unsat_core) 
                ctx.m_unsat_core.push_back(tr(e));
            break;
        default:
            break;
        }                                

        return result;
    }

}
