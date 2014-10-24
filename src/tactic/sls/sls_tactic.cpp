/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    sls_tactic.h

Abstract:

    A Stochastic Local Search (SLS) tactic

Author:

    Christoph (cwinter) 2012-02-29

Notes:

--*/
#include<iomanip>
#include"map.h"
#include"nnf.h"
#include"cooperate.h"
#include"ast_smt2_pp.h"
#include"ast_pp.h"
#include"var_subst.h"
#include"model_pp.h"
#include"model_evaluator.h"
#include"solve_eqs_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"simplify_tactic.h"
#include"stopwatch.h"
#include"propagate_values_tactic.h"
#include"sls_tactic.h"
#include"nnf_tactic.h"

#include"sls_params.hpp"
#include"sls_evaluator.h"
#include"sls_tracker.h"

class sls_tactic : public tactic {
    class stats {
    public:
        unsigned        m_restarts;
        stopwatch       m_stopwatch;    
        unsigned        m_full_evals;
        unsigned        m_incr_evals;
        unsigned        m_moves, m_flips, m_incs, m_decs, m_invs;
        stats() :
            m_restarts(0),
            m_full_evals(0),
            m_incr_evals(0),
            m_moves(0),
            m_flips(0),
            m_incs(0),
            m_decs(0),
            m_invs(0) {
                m_stopwatch.reset();
                m_stopwatch.start();
            }
        void reset() {
            m_full_evals = m_flips = m_incr_evals = 0;
            m_stopwatch.reset();
            m_stopwatch.start();
        }
    };    

    struct imp {       
        ast_manager   & m_manager;
        stats         & m_stats;
        unsynch_mpz_manager m_mpz_manager;
        powers          m_powers;
        mpz             m_zero, m_one, m_two;            
        bool            m_produce_models;
        volatile bool   m_cancel;    
        bv_util         m_bv_util;
        sls_tracker     m_tracker;
        sls_evaluator   m_evaluator;

        unsigned        m_max_restarts;
        unsigned        m_plateau_limit;

        typedef enum { MV_FLIP = 0, MV_INC, MV_DEC, MV_INV } move_type;        

        imp(ast_manager & m, params_ref const & p, stats & s) : 
            m_manager(m),
            m_stats(s),
            m_powers(m_mpz_manager),
            m_zero(m_mpz_manager.mk_z(0)),
            m_one(m_mpz_manager.mk_z(1)),
            m_two(m_mpz_manager.mk_z(2)),
            m_cancel(false),
            m_bv_util(m),
            m_tracker(m, m_bv_util, m_mpz_manager, m_powers),
            m_evaluator(m, m_bv_util, m_tracker, m_mpz_manager, m_powers) 
        {
            updt_params(p);
        }

        ~imp() {
            m_mpz_manager.del(m_zero);
            m_mpz_manager.del(m_one);
            m_mpz_manager.del(m_two);
        }        

        ast_manager & m() const { return m_manager; }

        void set_cancel(bool f) { m_cancel = f; }
        void cancel() { set_cancel(true); }
        void reset_cancel() { set_cancel(false); }

        static void collect_param_descrs(param_descrs & r) {
            sls_params::collect_param_descrs(r);
        }

        void updt_params(params_ref const & _p) {
            sls_params p(_p);
            m_produce_models = _p.get_bool("model", false);
            m_max_restarts = p.restarts();            
            m_tracker.set_random_seed(p.random_seed());
            m_plateau_limit = p.plateau_limit();
        }

        void checkpoint() { 
            if (m_cancel)
                throw tactic_exception(TACTIC_CANCELED_MSG);
            cooperate("sls");
        }

        bool full_eval(goal_ref const & g, model & mdl) {
            bool res = true;

            unsigned sz = g->size();
            for (unsigned i = 0; i < sz && res; i++) {
                checkpoint();
                expr_ref o(m_manager);

                if (!mdl.eval(g->form(i), o, true))
                    exit(ERR_INTERNAL_FATAL);

                res = m_manager.is_true(o.get());
            }        

            TRACE("sls", tout << "Evaluation: " << res << std::endl;);

            return res;
        }

        double top_score(goal_ref const & g) {
            #if 0
            double min = m_tracker.get_score(g->form(0));
            unsigned sz = g->size();
            for (unsigned i = 1; i < sz; i++) {
                double q = m_tracker.get_score(g->form(i));
                if (q < min) min = q;
            }
            TRACE("sls_top", tout << "Score distribution:"; 
                                for (unsigned i = 0; i < sz; i++)
                                    tout << " " << m_tracker.get_score(g->form(i));
                                tout << " MIN: " << min << std::endl; );
            return min;
            #else
            double top_sum = 0.0;
            unsigned sz = g->size();
            for (unsigned i = 0; i < sz; i++) {
                top_sum += m_tracker.get_score(g->form(i));
            }
            TRACE("sls_top", tout << "Score distribution:"; 
                                    for (unsigned i = 0; i < sz; i++)
                                        tout << " " << m_tracker.get_score(g->form(i));
                                    tout << " AVG: " << top_sum / (double) sz << std::endl; );
            return top_sum / (double) sz;
            #endif
        }

        double rescore(goal_ref const & g) {
            m_evaluator.update_all();
            m_stats.m_full_evals++;
            return top_score(g);
        }

        double incremental_score(goal_ref const & g, func_decl * fd, const mpz & new_value) {
            m_evaluator.update(fd, new_value);
            m_stats.m_incr_evals++;
            return top_score(g);
        }

        bool what_if(goal_ref const & g, func_decl * fd, const unsigned & fd_inx, const mpz & temp, 
                        double & best_score, unsigned & best_const, mpz & best_value) {
        
            #ifdef Z3DEBUG
            mpz old_value;
            m_mpz_manager.set(old_value, m_tracker.get_value(fd));
            #endif

            double r = incremental_score(g, fd, temp);
        
            #ifdef Z3DEBUG
            TRACE("sls_whatif", tout << "WHAT IF " << fd->get_name() << " WERE " << m_mpz_manager.to_string(temp) << 
                                        " --> " << r << std::endl; );
        
            m_mpz_manager.del(old_value);
            #endif

            if (r >= best_score) {
                best_score = r;
                best_const = fd_inx;            
                m_mpz_manager.set(best_value, temp);
                return true;
            }

            return false;
        }

        void mk_inc(unsigned bv_sz, const mpz & old_value, mpz & incremented) {
            unsigned shift;        
            m_mpz_manager.add(old_value, m_one, incremented);
            if (m_mpz_manager.is_power_of_two(incremented, shift) && shift == bv_sz)
                m_mpz_manager.set(incremented, m_zero);
        }

        void mk_dec(unsigned bv_sz, const mpz & old_value, mpz & decremented) {
            if (m_mpz_manager.is_zero(old_value)) {
                m_mpz_manager.set(decremented, m_powers(bv_sz));
                m_mpz_manager.dec(decremented);
            }
            else
                m_mpz_manager.sub(old_value, m_one, decremented);
        }

        void mk_inv(unsigned bv_sz, const mpz & old_value, mpz & inverted) {
            m_mpz_manager.bitwise_not(bv_sz, old_value, inverted);
        }

        void mk_flip(sort * s, const mpz & old_value, unsigned bit, mpz & flipped) {
            m_mpz_manager.set(flipped, m_zero);

            if (m_bv_util.is_bv_sort(s)) {
                mpz mask;
                m_mpz_manager.set(mask, m_powers(bit));
                m_mpz_manager.bitwise_xor(old_value, mask, flipped);
                m_mpz_manager.del(mask);
            }
            else if (m_manager.is_bool(s))
                m_mpz_manager.set(flipped, (m_mpz_manager.is_zero(old_value)) ? m_one : m_zero);
            else
                NOT_IMPLEMENTED_YET();
        }

        void mk_random_move(goal_ref const & g) {
            unsigned rnd_mv = 0;
            if (m_mpz_manager.is_one(m_tracker.get_random_bool())) rnd_mv=2;
            if (m_mpz_manager.is_one(m_tracker.get_random_bool())) rnd_mv++;
            move_type mt = (move_type) rnd_mv;

            // inversion doesn't make sense, let's do a flip instead.
            if (mt == MV_INV) mt = MV_FLIP;

            ptr_vector<func_decl> & unsat_constants = m_tracker.get_unsat_constants(g);                
            unsigned ucc = unsat_constants.size(); 
            unsigned rc = (m_tracker.get_random_uint((ucc < 16) ? 4 : (ucc < 256) ? 8 : (ucc < 4096) ? 12 : (ucc < 65536) ? 16 : 32)) % ucc;
            func_decl * fd = unsat_constants[rc];
            mpz new_value;
            unsigned bit = 0;

            switch (mt)
            {
            case MV_FLIP: {
                unsigned bv_sz = m_bv_util.get_bv_size(fd->get_range());
                bit = (m_tracker.get_random_uint((bv_sz < 16) ? 4 : (bv_sz < 256) ? 8 : (bv_sz < 4096) ? 12 : (bv_sz < 65536) ? 16 : 32)) % bv_sz;
                mk_flip(fd->get_range(), m_tracker.get_value(fd), bit, new_value);
                break;
            }
            case MV_INC: 
                mk_inc(m_bv_util.get_bv_size(fd->get_range()), m_tracker.get_value(fd), new_value);
                break;
            case MV_DEC: 
                mk_dec(m_bv_util.get_bv_size(fd->get_range()), m_tracker.get_value(fd), new_value);
                break;
            case MV_INV:
                mk_inv(m_bv_util.get_bv_size(fd->get_range()), m_tracker.get_value(fd), new_value);
                break;
            default:
                NOT_IMPLEMENTED_YET();
            }

            m_evaluator.update(fd, new_value);            

            TRACE("sls", tout << "Randomization candidates: ";
                         for (unsigned i = 0; i < unsat_constants.size(); i++)
                             tout << unsat_constants[i]->get_name() << ", ";
                         tout << std::endl;
                         tout << "Random move: ";
                         switch (mt) {
                         case MV_FLIP: tout << "Flip #" << bit << " in " << fd->get_name() << std::endl; break;
                         case MV_INC: tout << "+1 for " << fd->get_name() << std::endl; break;
                         case MV_DEC: tout << "-1 for " << fd->get_name() << std::endl; break;
                         case MV_INV: tout << "NEG for " << fd->get_name() << std::endl; break;
                         }
                         tout << "Locally randomized model: " << std::endl; m_tracker.show_model(tout); );            

            m_mpz_manager.del(new_value);
        }

        double find_best_move(goal_ref const & g, ptr_vector<func_decl> & to_evaluate, double score, 
                              unsigned & best_const, mpz & best_value, unsigned & new_bit, move_type & move) {
            mpz old_value, temp;
            unsigned bv_sz;
            double new_score = score;

            for (unsigned i = 0; i < to_evaluate.size() && new_score < 1.0 ; i++) {
                func_decl * fd = to_evaluate[i];
                sort * srt = fd->get_range();
                bv_sz = (m_manager.is_bool(srt)) ? 1 : m_bv_util.get_bv_size(srt);
                m_mpz_manager.set(old_value, m_tracker.get_value(fd));

                // first try to flip every bit
                for (unsigned j = 0; j < bv_sz && new_score < 1.0; j++) {
                    // What would happen if we flipped bit #i ?                
                    mk_flip(srt, old_value, j, temp);                

                    if (what_if(g, fd, i, temp, new_score, best_const, best_value)) {
                        new_bit = j;
                        move = MV_FLIP;
                    }
                }

                if (m_bv_util.is_bv_sort(srt) && bv_sz > 1) {
                    if (!m_mpz_manager.is_even(old_value)) { 
                        // for odd values, try +1
                        mk_inc(bv_sz, old_value, temp);
                        if (what_if(g, fd, i, temp, new_score, best_const, best_value))
                            move = MV_INC;
                    }
                    else { 
                        // for even values, try -1
                        mk_dec(bv_sz, old_value, temp);
                        if (what_if(g, fd, i, temp, new_score, best_const, best_value))
                            move = MV_DEC;
                    }

                    // try inverting
                    mk_inv(bv_sz, old_value, temp);
                    if (what_if(g, fd, i, temp, new_score, best_const, best_value))
                        move = MV_INV;
                }

                // reset to what it was before
                double check = incremental_score(g, fd, old_value);
                SASSERT(check == score);
            }

            m_mpz_manager.del(old_value);
            m_mpz_manager.del(temp);
            return new_score;
        }        

        lbool search(goal_ref const & g) {        
            lbool res = l_undef;
            double score = 0.0, old_score = 0.0;
            unsigned new_const = (unsigned)-1, new_bit = 0;        
            mpz new_value;
            move_type move;
            
            score = rescore(g);
            TRACE("sls", tout << "Starting search, initial score   = " << std::setprecision(32) << score << std::endl;
                         tout << "Score distribution:"; 
                         for (unsigned i = 0; i < g->size(); i++)
                             tout << " " << std::setprecision(3) << m_tracker.get_score(g->form(i));
                         tout << " TOP: " << score << std::endl; ); 
        
            unsigned plateau_cnt = 0;

            while (plateau_cnt < m_plateau_limit) {                

                do {
                    checkpoint();
            
                    old_score = score;
                    new_const = (unsigned)-1;
                        
                    ptr_vector<func_decl> & to_evaluate = m_tracker.get_unsat_constants(g);

                    TRACE("sls_constants", tout << "Evaluating these constants: " << std::endl;
                                            for (unsigned i = 0 ; i < to_evaluate.size(); i++)
                                                tout << to_evaluate[i]->get_name() << std::endl; );

                    score = find_best_move(g, to_evaluate, score, new_const, new_value, new_bit, move);

                    if (new_const == static_cast<unsigned>(-1)) {
                        TRACE("sls", tout << "Local maximum reached; unsatisfied constraints: " << std::endl; 
                                        for (unsigned i = 0; i < g->size(); i++) {
                                            if (!m_mpz_manager.is_one(m_tracker.get_value(g->form(i))))
                                                tout << mk_ismt2_pp(g->form(i), m_manager) << std::endl;
                                        });

                        TRACE("sls_max", m_tracker.show_model(tout);
                                        tout << "Scores: " << std::endl;
                                        for (unsigned i = 0; i < g->size(); i++)
                                            tout << mk_ismt2_pp(g->form(i), m_manager) << " ---> " << 
                                            m_tracker.get_score(g->form(i)) << std::endl; );
                        score = old_score;
                    }
                    else {
                        m_stats.m_moves++;
                        func_decl * fd = to_evaluate[new_const];

                        TRACE("sls", tout << "Setting " << fd->get_name() << " to " << m_mpz_manager.to_string(new_value) << " (Move: ";
                                        switch (move) {
                                        case MV_FLIP:  
                                            tout << "Flip";
                                            if (!m_manager.is_bool(fd->get_range())) tout << " #" << new_bit;
                                            break;
                                        case MV_INC: 
                                            tout << "+1";
                                            break;
                                        case MV_DEC: 
                                            tout << "-1";
                                            break;
                                        case MV_INV: 
                                            tout << "NEG";
                                            break;
                                        };                                        
                                        tout << ") ; new score = " << std::setprecision(32) << score << std::endl; );

                        switch (move) {
                        case MV_FLIP: m_stats.m_flips++; break;
                        case MV_INC: m_stats.m_incs++; break;
                        case MV_DEC: m_stats.m_decs++; break;
                        case MV_INV: m_stats.m_invs++; break;
                        }
                    
                        score = incremental_score(g, fd, new_value);    

                        TRACE("sls", tout << "Score distribution:"; 
                                        for (unsigned i = 0; i < g->size(); i++)
                                            tout << " " << std::setprecision(3) << m_tracker.get_score(g->form(i));
                                        tout << " TOP: " << score << std::endl; );                        
                    }

                    if (score >= 1.0) {
                        // score could theoretically be imprecise.
                        bool all_true = true;
                        for (unsigned i = 0; i < g->size() && all_true; i++)
                            if (!m_mpz_manager.is_one(m_tracker.get_value(g->form(i))))
                                all_true=false;
                        if (all_true) {
                            res = l_true; // sat
                            goto bailout;
                        } else
                            TRACE("sls", tout << "Imprecise 1.0 score" << std::endl;);
                    }
                }
                while (score > old_score && res == l_undef);                

                if (score != old_score)
                    plateau_cnt = 0;
                else {
                    plateau_cnt++;
                    if (plateau_cnt < m_plateau_limit) {
                        TRACE("sls", tout << "In a plateau (" << plateau_cnt << "/" << m_plateau_limit << "); randomizing locally." << std::endl; );
                        m_evaluator.randomize_local(g);
                        //mk_random_move(g);
                        score = top_score(g);
                    }
                }
            }

            bailout:
            m_mpz_manager.del(new_value);

            return res;
        }    

        void operator()(goal_ref const & g, model_converter_ref & mc) {
            if (g->inconsistent()) {
                mc = 0;
                return;
            }

            m_tracker.initialize(g);
            lbool res = l_undef;
        
            do {
                checkpoint();
                if ((m_stats.m_restarts % 100) == 0)                        
                    report_tactic_progress("Searching... restarts left:", m_max_restarts - m_stats.m_restarts);
                
                res = search(g);

                if (res == l_undef)
                    m_tracker.randomize();
            }
            while (res != l_true && m_stats.m_restarts++ < m_max_restarts);
        
            if (res == l_true) {                
                if (m_produce_models) {
                    model_ref mdl = m_tracker.get_model();
                    mc = model2model_converter(mdl.get());
                    TRACE("sls_model", mc->display(tout); );
                }
                g->reset();
            }
            else
                mc = 0;
        }
    };
    
    ast_manager    & m;
    params_ref       m_params;
    imp            * m_imp;
    stats            m_stats;

public:
    sls_tactic(ast_manager & _m, params_ref const & p):
        m(_m),
        m_params(p) {
        m_imp = alloc(imp, m, p, m_stats);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(sls_tactic, m, m_params);
    }

    virtual ~sls_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
        imp::collect_param_descrs(r);
    }
    
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        m_imp->m_produce_models = g->models_enabled();        
        mc = 0; pc = 0; core = 0; result.reset();
        
        TRACE("sls", g->display(tout););
        tactic_report report("sls", *g);
        
        m_imp->operator()(g, mc);

        g->inc_depth();
        result.push_back(g.get());
        TRACE("sls", g->display(tout););
        SASSERT(g->is_well_sorted());
    }

    virtual void cleanup() {        
        imp * d = alloc(imp, m, m_params, m_stats);
        #pragma omp critical (tactic_cancel)
        {
            std::swap(d, m_imp);
        }
        dealloc(d);
    }
    
    virtual void collect_statistics(statistics & st) const {
        double seconds = m_stats.m_stopwatch.get_current_seconds();            
        st.update("sls restarts", m_stats.m_restarts);
        st.update("sls full evals", m_stats.m_full_evals);
        st.update("sls incr evals", m_stats.m_incr_evals);
        st.update("sls incr evals/sec", m_stats.m_incr_evals/ seconds);
        st.update("sls FLIP moves", m_stats.m_flips);    
        st.update("sls INC moves", m_stats.m_incs);
        st.update("sls DEC moves", m_stats.m_decs);
        st.update("sls INV moves", m_stats.m_invs);
        st.update("sls moves", m_stats.m_moves);
        st.update("sls moves/sec", m_stats.m_moves / seconds);
    }

    virtual void reset_statistics() {
        m_stats.reset();
    }

    virtual void set_cancel(bool f) {
        if (m_imp)
            m_imp->set_cancel(f);
    }
};

tactic * mk_sls_tactic(ast_manager & m, params_ref const & p) {
    return and_then(fail_if_not(mk_is_qfbv_probe()), // Currently only QF_BV is supported.
                    clean(alloc(sls_tactic, m, p)));
}


tactic * mk_preamble(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    // main_p.set_bool("pull_cheap_ite", true);
    main_p.set_bool("push_ite_bv", true);
    main_p.set_bool("blast_distinct", true);
    // main_p.set_bool("udiv2mul", true);
    main_p.set_bool("hi_div0", true);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    params_ref hoist_p;
    hoist_p.set_bool("hoist_mul", true);
    // hoist_p.set_bool("hoist_cmul", true);
    hoist_p.set_bool("som", false);

    params_ref gaussian_p;
    // conservative gaussian elimination. 
    gaussian_p.set_uint("gaussian_max_occs", 2); 

    return and_then(and_then(mk_simplify_tactic(m),                             
                             mk_propagate_values_tactic(m),
                             using_params(mk_solve_eqs_tactic(m), gaussian_p),
                             mk_elim_uncnstr_tactic(m),
                             mk_bv_size_reduction_tactic(m),
                             using_params(mk_simplify_tactic(m), simp2_p)),
                        using_params(mk_simplify_tactic(m), hoist_p),
                        mk_max_bv_sharing_tactic(m),
                        mk_nnf_tactic(m, p));
}

tactic * mk_qfbv_sls_tactic(ast_manager & m, params_ref const & p) {
    tactic * t = and_then(mk_preamble(m, p), mk_sls_tactic(m));    
    t->updt_params(p);
    return t;
}
