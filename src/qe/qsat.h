/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qsat.h

Abstract:

    Quantifier Satisfiability Solver.

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-28

Revision History:


--*/

#ifndef __QE_MBP_H__
#define __QE_MBP_H__

#include "tactic.h"

namespace qe {
    class qsat : public tactic {
        class impl;
        impl * m_impl;
    public:
        qsat(ast_manager& m);
        ~qsat();
        
        virtual void updt_params(params_ref const & p);
        virtual void collect_param_descrs(param_descrs & r);
        virtual void operator()(/* in */  goal_ref const & in, 
                                /* out */ goal_ref_buffer & result, 
                                /* out */ model_converter_ref & mc, 
                                /* out */ proof_converter_ref & pc,
                                /* out */ expr_dependency_ref & core);
        
        virtual void collect_statistics(statistics & st) const;
        virtual void reset_statistics();
        virtual void cleanup() = 0;
        virtual void set_logic(symbol const & l);
        virtual void set_progress_callback(progress_callback * callback);
        virtual tactic * translate(ast_manager & m);
        
    };
};

#endif 
