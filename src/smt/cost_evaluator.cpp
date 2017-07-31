/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    cost_evaluator.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-14.

Revision History:

--*/
#include "smt/cost_evaluator.h"
#include "util/warning.h"

cost_evaluator::cost_evaluator(ast_manager & m):
    m_manager(m), 
    m_util(m) {
}

float cost_evaluator::eval(expr * f) const {
#define E(IDX) eval(to_app(f)->get_arg(IDX))
    if (is_app(f)) {
        unsigned num_args;
        family_id fid = to_app(f)->get_family_id();
        if (fid == m_manager.get_basic_family_id()) {
            switch (to_app(f)->get_decl_kind()) {
            case OP_TRUE:     return 1.0f;
            case OP_FALSE:    return 0.0f;
            case OP_NOT:      return E(0) == 0.0f ? 1.0f : 0.0f;
            case OP_AND:      
                num_args = to_app(f)->get_num_args();
                for (unsigned i = 0; i < num_args; i++) 
                    if (E(i) == 0.0f)
                        return 0.0f;
                return 1.0f;
            case OP_OR:
                num_args = to_app(f)->get_num_args();
                for (unsigned i = 0; i < num_args; i++) 
                    if (E(i) != 0.0f)
                        return 1.0f;
                return 0.0f;
            case OP_ITE:      return E(0) != 0.0f ? E(1) : E(2);
            case OP_EQ:
            case OP_IFF:      return E(0) == E(1) ? 1.0f : 0.0f;
            case OP_XOR:      return E(0) != E(1) ? 1.0f : 0.0f;
            case OP_IMPLIES:  
                if (E(0) == 0.0f)
                    return 1.0f;
                return E(1) != 0.0f ? 1.0f : 0.0f;
            default:
                ;
            }
        }
        else if (fid == m_util.get_family_id()) {
            switch (to_app(f)->get_decl_kind()) {
            case OP_NUM: {
                rational r = to_app(f)->get_decl()->get_parameter(0).get_rational();
                return static_cast<float>(numerator(r).get_int64())/static_cast<float>(denominator(r).get_int64());
            } 
            case OP_LE:       return E(0) <= E(1) ? 1.0f : 0.0f;
            case OP_GE:       return E(0) >= E(1) ? 1.0f : 0.0f;
            case OP_LT:       return E(0) <  E(1) ? 1.0f : 0.0f;
            case OP_GT:       return E(0) >  E(1) ? 1.0f : 0.0f;
            case OP_ADD:      return E(0) + E(1);
            case OP_SUB:      return E(0) - E(1);
            case OP_UMINUS:   return - E(0);
            case OP_MUL:      return E(0) * E(1);
            case OP_DIV: {     
                float q = E(1);
                if (q == 0.0f) {
                    warning_msg("cost function division by zero");
                    return 1.0f;
                }
                return E(0) / q;
            }
            default:
                ;
            }
        }
    }
    else if (is_var(f)) {
        unsigned idx = to_var(f)->get_idx();
        if (idx < m_num_args)
            return m_args[m_num_args - idx - 1];
    }
    warning_msg("cost function evaluation error");
    return 1.0f;
}

float cost_evaluator::operator()(expr * f, unsigned num_args, float const * args) {
    m_num_args = num_args;
    m_args     = args;
    return eval(f);
}



