/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_elim_eqs.h

Abstract:

    Helper class for eliminating eqs.

Author:

    Leonardo de Moura (leonardo) 2011-05-27.

Revision History:

--*/
#ifndef SAT_ELIM_EQS_H_
#define SAT_ELIM_EQS_H_

#include"sat_types.h"

namespace sat {
    class solver;
    
    class elim_eqs {
        solver & m_solver;
        void save_elim(literal_vector const & roots, bool_var_vector const & to_elim);
        void cleanup_clauses(literal_vector const & roots, clause_vector & cs);
        void cleanup_bin_watches(literal_vector const & roots);
        bool check_clauses(literal_vector const & roots) const;
    public:
        elim_eqs(solver & s);
        void operator()(literal_vector const & roots, bool_var_vector const & to_elim);
    };

};

#endif
