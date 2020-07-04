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
#pragma once

#include "util/stopwatch.h"
#include "util/lbool.h"
#include "tactic/model_converter.h"
#include "tactic/goal.h"

#include "tactic/sls/sls_tracker.h"
#include "tactic/sls/sls_evaluator.h"
#include "util/statistics.h"

class sls_engine {
public:
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

protected:
    ast_manager   & m_manager;
    stats           m_stats;
    unsynch_mpz_manager m_mpz_manager;
    powers          m_powers;
    mpz             m_zero, m_one, m_two;
    bool            m_produce_models;
    bv_util         m_bv_util;
    sls_tracker     m_tracker;
    sls_evaluator   m_evaluator;
    ptr_vector<expr> m_assertions;

    unsigned        m_max_restarts;
    unsigned        m_walksat;
    unsigned        m_walksat_repick;
    unsigned        m_wp;
    unsigned        m_vns_mc;
    unsigned        m_vns_repick;
    unsigned        m_paws;
    unsigned        m_paws_sp;
    unsigned        m_restart_base;
    unsigned        m_restart_next;
    unsigned        m_restart_init;
    unsigned        m_early_prune;
    unsigned        m_random_offset;
    unsigned        m_rescore;

    typedef enum { MV_FLIP = 0, MV_INC, MV_DEC, MV_INV } move_type;

public:    
    sls_engine(ast_manager & m, params_ref const & p);
    ~sls_engine();

    ast_manager & m() const { return m_manager; }


    void updt_params(params_ref const & _p);

    void assert_expr(expr * e) { m_assertions.push_back(e); }

    // stats const & get_stats(void) { return m_stats; }
    void collect_statistics(statistics & st) const;
    void reset_statistics() { m_stats.reset(); }

    bool full_eval(model & mdl);

    void mk_add(unsigned bv_sz, const mpz & old_value, mpz & add_value, mpz & result);
    void mk_inc(unsigned bv_sz, const mpz & old_value, mpz & incremented);
    void mk_dec(unsigned bv_sz, const mpz & old_value, mpz & decremented);
    void mk_inv(unsigned bv_sz, const mpz & old_value, mpz & inverted);
    void mk_flip(sort * s, const mpz & old_value, unsigned bit, mpz & flipped);            

    lbool search();

    lbool operator()();
    void operator()(goal_ref const & g, model_converter_ref & mc);

protected:
    void checkpoint();

    bool what_if(func_decl * fd, const unsigned & fd_inx, const mpz & temp,
                 double & best_score, unsigned & best_const, mpz & best_value);

    double top_score();
    double rescore();
    double serious_score(func_decl * fd, const mpz & new_value);
    double incremental_score(func_decl * fd, const mpz & new_value);

    double incremental_score_prune(func_decl * fd, const mpz & new_value);
    double find_best_move(ptr_vector<func_decl> & to_evaluate, double score,
                          unsigned & best_const, mpz & best_value, unsigned & new_bit, move_type & move);

    double find_best_move_mc(ptr_vector<func_decl> & to_evaluate, double score,
                          unsigned & best_const, mpz & best_value);

    void mk_random_move(ptr_vector<func_decl> & unsat_constants);

    //double get_restart_armin(unsigned cnt_restarts);    
    unsigned check_restart(unsigned curr_value);
};

