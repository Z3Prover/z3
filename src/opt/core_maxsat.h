/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    core_maxsat.h

Abstract:
    Core and SAT guided MaxSAT with cardinality constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-9

Notes:

--*/
#ifndef _OPT_CORE_MAXSAT_H_
#define _OPT_CORE_MAXSAT_H_

#include "solver.h"
#include "maxsmt.h"

namespace opt {

    class core_maxsat : public maxsmt_solver {
        typedef obj_hashtable<expr> expr_set;

        ast_manager&    m;
        solver&         s;
        expr_ref_vector m_soft;
        expr_ref_vector m_answer;
        unsigned        m_upper;
    public:
        core_maxsat(ast_manager& m, solver& s, expr_ref_vector& soft_constraints);
        virtual ~core_maxsat();
        virtual lbool operator()();
        virtual rational get_lower() const;
        virtual rational get_upper() const;
        virtual rational get_value() const;
        virtual expr_ref_vector get_assignment() const;
        virtual void set_cancel(bool f);

    private:
        void set2vector(expr_set const& set, ptr_vector<expr>& es) const;
        expr_ref mk_at_most(expr_set const& set, unsigned k);
    };
    
};

#endif
