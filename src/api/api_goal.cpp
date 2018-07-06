/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_goal.cpp

Abstract:
    API for creating goals
    
Author:

    Leonardo de Moura (leonardo) 2012-03-06.

Revision History:

--*/
#include<iostream>
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_goal.h"
#include "ast/ast_translation.h"
#include "api/api_model.h"

extern "C" {

    Z3_goal Z3_API Z3_mk_goal(Z3_context c, Z3_bool models, Z3_bool unsat_cores, Z3_bool proofs) {
        Z3_TRY;
        LOG_Z3_mk_goal(c, models, unsat_cores, proofs);
        RESET_ERROR_CODE();
        if (proofs != 0 && !mk_c(c)->m().proofs_enabled()) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "proofs are required, but proofs are not enabled on the context");
            RETURN_Z3(nullptr);
        }
        Z3_goal_ref * g = alloc(Z3_goal_ref, *mk_c(c));
        g->m_goal       = alloc(goal, mk_c(c)->m(), proofs != 0, models != 0, unsat_cores != 0);
        mk_c(c)->save_object(g);
        Z3_goal r       = of_goal(g);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_goal_inc_ref(Z3_context c, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_goal_inc_ref(c, g);
        RESET_ERROR_CODE();
        to_goal(g)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_goal_dec_ref(Z3_context c, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_goal_dec_ref(c, g);
        RESET_ERROR_CODE();
        to_goal(g)->dec_ref();
        Z3_CATCH;
    }

    Z3_goal_prec Z3_API Z3_goal_precision(Z3_context c, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_goal_precision(c, g);
        RESET_ERROR_CODE();
        switch (to_goal_ref(g)->prec()) {
        case goal::PRECISE: return Z3_GOAL_PRECISE;
        case goal::UNDER:   return Z3_GOAL_UNDER;
        case goal::OVER:    return Z3_GOAL_OVER;
        case goal::UNDER_OVER: return Z3_GOAL_UNDER_OVER;
        default:
            UNREACHABLE();
            return Z3_GOAL_UNDER_OVER;
        }
        Z3_CATCH_RETURN(Z3_GOAL_UNDER_OVER);
    }

    void Z3_API Z3_goal_assert(Z3_context c, Z3_goal g, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_goal_assert(c, g, a);
        RESET_ERROR_CODE();
        CHECK_FORMULA(a,);        
        to_goal_ref(g)->assert_expr(to_expr(a));
        Z3_CATCH;
    }

    Z3_bool Z3_API Z3_goal_inconsistent(Z3_context c, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_goal_inconsistent(c, g);
        RESET_ERROR_CODE();
        return to_goal_ref(g)->inconsistent();
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    unsigned Z3_API Z3_goal_depth(Z3_context c, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_goal_depth(c, g);
        RESET_ERROR_CODE();
        return to_goal_ref(g)->depth();
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_goal_reset(Z3_context c, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_goal_reset(c, g);
        RESET_ERROR_CODE();
        to_goal_ref(g)->reset();
        Z3_CATCH;
    }

    unsigned Z3_API Z3_goal_size(Z3_context c, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_goal_size(c, g);
        RESET_ERROR_CODE();
        return to_goal_ref(g)->size();
        Z3_CATCH_RETURN(0);
    }
    
    Z3_ast Z3_API Z3_goal_formula(Z3_context c, Z3_goal g, unsigned idx) {
        Z3_TRY;
        LOG_Z3_goal_formula(c, g, idx);
        RESET_ERROR_CODE();
        if (idx >= to_goal_ref(g)->size()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        expr * result = to_goal_ref(g)->form(idx);
        mk_c(c)->save_ast_trail(result);
        RETURN_Z3(of_ast(result));
        Z3_CATCH_RETURN(nullptr);
    }
    
    unsigned Z3_API Z3_goal_num_exprs(Z3_context c, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_goal_num_exprs(c, g);
        RESET_ERROR_CODE();
        return to_goal_ref(g)->num_exprs();
        Z3_CATCH_RETURN(0);
    }
    
    Z3_bool Z3_API Z3_goal_is_decided_sat(Z3_context c, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_goal_is_decided_sat(c, g);
        RESET_ERROR_CODE();
        return to_goal_ref(g)->is_decided_sat();
        Z3_CATCH_RETURN(Z3_FALSE);
    }
    
    Z3_bool Z3_API Z3_goal_is_decided_unsat(Z3_context c, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_goal_is_decided_unsat(c, g);
        RESET_ERROR_CODE();
        return to_goal_ref(g)->is_decided_unsat();
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_model Z3_API Z3_goal_convert_model(Z3_context c, Z3_goal g, Z3_model m) {
        Z3_TRY;
        LOG_Z3_goal_convert_model(c, g, m);
        RESET_ERROR_CODE();
        model_ref new_m;
        Z3_model_ref * m_ref = alloc(Z3_model_ref, *mk_c(c)); 
        mk_c(c)->save_object(m_ref);
        if (m) m_ref->m_model = to_model_ref(m)->copy(); 
        if (to_goal_ref(g)->mc()) 
            (*to_goal_ref(g)->mc())(m_ref->m_model);
        RETURN_Z3(of_model(m_ref));
        Z3_CATCH_RETURN(0);
    }    

    Z3_goal Z3_API Z3_goal_translate(Z3_context c, Z3_goal g, Z3_context target) {
        Z3_TRY;
        LOG_Z3_goal_translate(c, g, target);
        RESET_ERROR_CODE();
        ast_translation translator(mk_c(c)->m(), mk_c(target)->m());
        Z3_goal_ref * _r = alloc(Z3_goal_ref, *mk_c(target));
        _r->m_goal       = to_goal_ref(g)->translate(translator);
        mk_c(target)->save_object(_r);
        Z3_goal r = of_goal(_r);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_string Z3_API Z3_goal_to_string(Z3_context c, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_goal_to_string(c, g);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        to_goal_ref(g)->display(buffer);
        // Hack for removing the trailing '\n'
        std::string result = buffer.str();
        SASSERT(result.size() > 0);
        result.resize(result.size()-1);
        return mk_c(c)->mk_external_string(result);
        Z3_CATCH_RETURN("");
    }

    Z3_string Z3_API Z3_goal_to_dimacs_string(Z3_context c, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_goal_to_dimacs_string(c, g);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        if (!to_goal_ref(g)->is_cnf()) { 
            SET_ERROR_CODE(Z3_INVALID_ARG, "If this is not what you want, then preprocess by optional bit-blasting and applying tseitin-cnf");
            RETURN_Z3(nullptr);
        }
        to_goal_ref(g)->display_dimacs(buffer);
        // Hack for removing the trailing '\n'
        std::string result = buffer.str();
        SASSERT(result.size() > 0);
        result.resize(result.size()-1);
        return mk_c(c)->mk_external_string(result);
        Z3_CATCH_RETURN("");
    }

};
