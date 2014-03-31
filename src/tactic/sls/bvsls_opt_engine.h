/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    bvsls_opt_engine.h

Abstract:

    Optimization extensions to bvsls

Author:

    Christoph (cwinter) 2014-03-28

Notes:

--*/
#ifndef _BVSLS_OPT_ENGINE_H_
#define _BVSLS_OPT_ENGINE_H_

#include "sls_engine.h"

class bvsls_opt_engine : public sls_engine {
    sls_tracker   & m_hard_tracker;
    sls_tracker     m_obj_tracker;
    sls_evaluator   m_obj_evaluator;
    model_ref       m_best_model;
    mpz             m_best_model_score;
    
public:
    bvsls_opt_engine(ast_manager & m, params_ref const & p);
    ~bvsls_opt_engine();

    class optimization_result {
    public:
        lbool is_sat;
        expr_ref optimum;
        optimization_result(ast_manager & m) : is_sat(l_undef), optimum(m) {}
    };

    optimization_result optimize(expr_ref const & objective, model_ref initial_model = model_ref(), bool maximize=true);

    void get_model(model_ref & result) { result = m_best_model; }

protected:
    expr_ref maximize(expr_ref const & objective);
    expr_ref minimize(expr_ref const & objective);

    bool what_if(func_decl * fd, const unsigned & fd_inx, const mpz & temp, 
                 mpz & best_score, unsigned & best_const, mpz & best_value);

    mpz find_best_move(ptr_vector<func_decl> & to_evaluate, mpz score,
                       unsigned & best_const, mpz & best_value, unsigned & new_bit, move_type & move,
                       mpz const & max_score, expr * objective);

    mpz top_score(void) {
        mpz res(0);
        obj_hashtable<expr> const & top_exprs = m_obj_tracker.get_top_exprs();
        for (obj_hashtable<expr>::iterator it = top_exprs.begin();
             it != top_exprs.end();
             it++)
             m_mpz_manager.add(res, m_obj_tracker.get_value(*it), res);
        return res;
    }

    void save_model(mpz const & score);
    bool randomize_wrt_hard();
};

#endif