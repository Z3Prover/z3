/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sls_engine.h

Abstract:

    A Stochastic Local Search (SLS) engine

Author:

    Christoph (cwinter) 2014-03-19

Notes:

--*/
#ifndef _SLS_ENGINE_H_
#define _SLS_ENGINE_H_

#include"stopwatch.h"
#include"lbool.h"
#include"model_converter.h"
#include"goal.h"

#include"sls_compilation_settings.h"
#include"sls_tracker.h"
#include"sls_evaluator.h"

class sls_engine {
public:
    class stats {
    public:
        unsigned        m_restarts;
        stopwatch       m_stopwatch;
        unsigned        m_full_evals;
        unsigned        m_incr_evals;
        unsigned        m_moves, m_flips, m_incs, m_decs, m_invs, m_umins, m_mul2s, m_mul3s, m_div2s;

        stats() :
            m_restarts(0),
            m_full_evals(0),
            m_incr_evals(0),
            m_moves(0),
            m_umins(0),
            m_mul2s(0),
            m_mul3s(0),
            m_div2s(0),
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

protected:
    ast_manager   & m_manager;
    stats           m_stats;
    unsynch_mpz_manager m_mpz_manager;
    powers          m_powers;
    mpz             m_zero, m_one, m_two;
    bool            m_produce_models;
    volatile bool   m_cancel;
    bv_util         m_bv_util;
    sls_tracker     m_tracker;
    sls_evaluator   m_evaluator;
    ptr_vector<expr> m_assertions;

    unsigned		m_restart_limit;
    unsigned        m_max_restarts;
    unsigned        m_plateau_limit;

    ptr_vector<mpz> m_old_values;

    typedef enum { MV_FLIP = 0, MV_INC, MV_DEC, MV_INV, MV_UMIN, MV_MUL2, MV_MUL3, MV_DIV2 } move_type;

public:    
    sls_engine(ast_manager & m, params_ref const & p);
    ~sls_engine();

    ast_manager & m() const { return m_manager; }

    void set_cancel(bool f) { m_cancel = f; }
    void cancel() { set_cancel(true); }
    void reset_cancel() { set_cancel(false); }

    void updt_params(params_ref const & _p);

    void assert_expr(expr * e) { m_assertions.push_back(e); }

    stats const & get_stats(void) { return m_stats; }
    void reset_statistics(void) { m_stats.reset(); }    

    bool full_eval(model & mdl);

    void mk_add(unsigned bv_sz, const mpz & old_value, mpz & add_value, mpz & result);
    void mk_mul2(unsigned bv_sz, const mpz & old_value, mpz & result);
    void mk_div2(unsigned bv_sz, const mpz & old_value, mpz & result);
    void mk_inc(unsigned bv_sz, const mpz & old_value, mpz & incremented);
    void mk_dec(unsigned bv_sz, const mpz & old_value, mpz & decremented);
    void mk_inv(unsigned bv_sz, const mpz & old_value, mpz & inverted);
    void mk_flip(sort * s, const mpz & old_value, unsigned bit, mpz & flipped);            

    void init_tracker(void);

    lbool search(void);    

    lbool operator()();
    void operator()(goal_ref const & g, model_converter_ref & mc);

protected:
    void checkpoint();
    double get_restart_armin(unsigned cnt_restarts);    

    bool what_if(func_decl * fd, const unsigned & fd_inx, const mpz & temp,
                 double & best_score, unsigned & best_const, mpz & best_value);
    bool what_if(expr * e, func_decl * fd, const mpz & temp,
                 double & best_score, mpz & best_value, unsigned i);
    bool what_if_local(expr * e, func_decl * fd, const unsigned & fd_inx, const mpz & temp,
                       double & best_score, unsigned & best_const, mpz & best_value);

    double top_score();
    double rescore();
    double serious_score(func_decl * fd, const mpz & new_value);
    double incremental_score(func_decl * fd, const mpz & new_value);

#if _EARLY_PRUNE_
    double incremental_score_prune(func_decl * fd, const mpz & new_value);
#endif
    double find_best_move(ptr_vector<func_decl> & to_evaluate, double score,
                          unsigned & best_const, mpz & best_value, unsigned & new_bit, move_type & move);
    double find_best_move_local(expr * e, func_decl * fd, mpz & best_value, unsigned i);
    double find_best_move_local(expr * e, ptr_vector<func_decl> & to_evaluate,
                                unsigned & best_const, mpz & best_value, unsigned & new_bit, move_type & move);    
    double find_best_move_vns(ptr_vector<func_decl> & to_evaluate, double score,
                              unsigned & best_const, mpz & best_value, unsigned & new_bit, move_type & move);    
    void mk_random_move(ptr_vector<func_decl> & unsat_constants);
    void mk_random_move();

    bool handle_plateau(void);
    bool handle_plateau(double old_score);

    inline unsigned check_restart(unsigned curr_value);
};

#endif
