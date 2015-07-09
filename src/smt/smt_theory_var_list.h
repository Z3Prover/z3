/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_theory_var_list.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#ifndef SMT_THEORY_VAR_LIST_H_
#define SMT_THEORY_VAR_LIST_H_

#include"smt_types.h"

namespace smt {

    class theory_var_list {
        int               m_th_id:8;
        int               m_th_var:24;
        theory_var_list * m_next;
        
    public:
        theory_var_list():
            m_th_id(null_theory_id),
            m_th_var(null_theory_var), 
            m_next(0) {
        }
        
        theory_var_list(theory_id t, theory_var v, theory_var_list * n = 0):
            m_th_id(t),
            m_th_var(v),
            m_next(n) {
        }
        
        theory_id get_th_id() const {
            return m_th_id;
        }
        
        theory_var get_th_var() const {
            return m_th_var;
        }
        
        theory_var_list * get_next() const {
            return m_next;
        }
        
        void set_th_id(theory_id id) {
            m_th_id = id;
        }
        
        void set_th_var(theory_var v) {
            m_th_var = v;
        }
        
        void set_next(theory_var_list * next) {
            m_next = next;
        }
    };

    // 32 bit machine
    COMPILE_TIME_ASSERT(sizeof(expr*) != 4 || sizeof(theory_var_list) == sizeof(theory_var_list *) + sizeof(int)); 
    // 64 bit machine
    COMPILE_TIME_ASSERT(sizeof(expr*) != 8 || sizeof(theory_var_list) == sizeof(theory_var_list *) + sizeof(int) + /* a structure must be aligned */ sizeof(int)); 
};

#endif /* SMT_THEORY_VAR_LIST_H_ */

