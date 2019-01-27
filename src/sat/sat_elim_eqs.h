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

#include "sat/sat_types.h"

namespace sat {
    class solver;
    class tmp_clause;
    
    class elim_eqs {
        struct bin {
            literal l1, l2;
            bool learned;
            bin(literal l1, literal l2, bool learned): l1(l1), l2(l2), learned(learned) {}
        };
        svector<bin> m_new_bin;
        solver & m_solver;
        tmp_clause* m_to_delete;
        void drat_delete_clause();
        void save_elim(literal_vector const & roots, bool_var_vector const & to_elim);
        void cleanup_clauses(literal_vector const & roots, clause_vector & cs);
        void cleanup_bin_watches(literal_vector const & roots);
        bool check_clauses(literal_vector const & roots) const;
        bool check_clause(clause const& c, literal_vector const& roots) const;
    public:
        elim_eqs(solver & s);
        ~elim_eqs();
        void operator()(literal_vector const & roots, bool_var_vector const & to_elim);
    };

};

#endif
