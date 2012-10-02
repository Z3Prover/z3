/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_eq_resolution.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-14.

Revision History:

--*/
#ifndef _SPC_EQ_RESOLUTION_H_
#define _SPC_EQ_RESOLUTION_H_

#include"spc_unary_inference.h"
#include"spc_statistics.h"

namespace spc {

    /**
       \brief Functor for applying equality resolution.

       s != t or R
       ==>
       sigma(R)
    */
    class eq_resolution : public unary_inference { 
    protected:
        statistics & m_stats;
        family_id    m_spc_fid;
        virtual justification * mk_justification(justification * parent, unsigned num_lits, literal * new_lits) {
            return mk_eq_res_justification(m_manager, m_spc_fid, parent, num_lits, new_lits);
        }
    public:
        eq_resolution(ast_manager & m, order & ord, statistics & stats):unary_inference(m, ord), m_stats(stats), m_spc_fid(m.get_family_id("spc")) {}
        virtual ~eq_resolution() {}
        void operator()(clause * cls, ptr_vector<clause> & new_clauses);
    };
};


#endif /* _SPC_EQ_RESOLUTION_H_ */

