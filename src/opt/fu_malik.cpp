/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    fu_malik.cpp

Abstract:
    Fu&Malik built-in optimization method.
    Adapted from sample code.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-15

Notes:

--*/

#include "fu_malik.h"

/**
   \brief Fu & Malik procedure for MaxSAT. This procedure is based on 
   unsat core extraction and the at-most-one constraint.

   Return the number of soft-constraints that can be
   satisfied.  Return -1 if the hard-constraints cannot be
   satisfied. That is, the formula cannot be satisfied even if all
   soft-constraints are ignored.

   For more information on the Fu & Malik procedure:

   Z. Fu and S. Malik, On solving the partial MAX-SAT problem, in International
   Conference on Theory and Applications of Satisfiability Testing, 2006.
*/
namespace opt {

    class fu_malik {
        ast_manager& m;
        solver& s;
        expr_ref_vector m_soft;
        expr_ref_vector m_aux;
    public:
        fu_malik(ast_manager& m, solver& s, expr_ref_vector const& soft):
            m(m),
            s(s),
            m_soft(soft),
            m_aux(m)
        {
            for (unsigned i = 0; i < m_soft.size(); i++) {
                m_aux.push_back(m.mk_fresh_const("p", m.mk_bool_sort()));
                s.assert_expr(m.mk_or(soft[i], m_aux[i].get()));
            }
        }


        /**
           \brief One step of the Fu&Malik algorithm.
           
           Input:    soft constraints + aux-vars (aka answer literals) 
           Output:   done/not-done  when not done return updated set of soft-constraints and aux-vars. 
           - if SAT --> terminates
           - if UNSAT 
           * compute unsat core
           * add blocking variable to soft-constraints in the core
           - replace soft-constraint with the one with the blocking variable
           - we should also add an aux-var
           - replace aux-var with a new one
           * add at-most-one constraint with blocking 
        */

        bool step() {
            expr_ref_vector assumptions(m), block_vars(m);
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                assumptions.push_back(m.mk_not(m_aux[i].get()));
            }
            lbool is_sat = s.check_sat(assumptions.size(), assumptions.c_ptr());
            if (is_sat != l_false) {
                return true;
            }

            ptr_vector<expr> core;
            s.get_unsat_core(core);

            // update soft-constraints and aux_vars
            for (unsigned i = 0; i < m_soft.size(); i++) {
                
                bool found = false;
                for (unsigned j = 0; !found && j < core.size(); ++j) {
                    found = m_soft[i].get() == core[j];
                }
                if (!found) {
                    continue;
                }
                expr_ref block_var(m);
                block_var = m.mk_fresh_const("block_var", m.mk_bool_sort());
                m_aux[i] = m.mk_fresh_const("aux", m.mk_bool_sort());
                m_soft[i] = m.mk_or(m_soft[i].get(), block_var);
                block_vars.push_back(block_var);
                s.assert_expr(m.mk_or(m_soft[i].get(), m_aux[i].get()));
            }
            assert_at_most_one(block_vars);
            return false;
        }

    private:

        void assert_at_most_one(expr_ref_vector const& block_vars) {
            expr_ref has_one(m), no_one(m), at_most_one(m);
            mk_at_most_one(block_vars.size(), block_vars.c_ptr(), has_one, no_one);
            at_most_one = m.mk_or(has_one, no_one);
            s.assert_expr(at_most_one);
        }

        void mk_at_most_one(unsigned n, expr* const * vars, expr_ref& has_one, expr_ref& no_one) {
            if (n == 1) {
                has_one = vars[0];
                no_one = m.mk_not(vars[0]);
            }
            else {
                unsigned mid = n/2;
                expr_ref has_one1(m), has_one2(m), no_one1(m), no_one2(m);
                mk_at_most_one(mid,   vars,     has_one1, no_one1);
                mk_at_most_one(n-mid, vars+mid, has_one2, no_one2);
                has_one = m.mk_or(m.mk_and(has_one1, no_one2), m.mk_and(has_one2, no_one1));
                no_one  = m.mk_and(no_one1, no_one2);
            }
        }

    };

    // TBD: the vector of soft constraints gets updated
    // but we really want to return the maximal set of
    // original soft constraints that are satisfied.
    // so we need to read out of the model what soft constraints
    // were satisfied. 

    
    lbool fu_malik_maxsat(solver& s, expr_ref_vector& soft_constraints) {
        ast_manager m = soft_constraints.get_manager();
        lbool is_sat = s.check_sat(0,0);
        if (!soft_constraints.empty() && is_sat == l_true) {
            s.push();
            fu_malik fm(m, s, soft_constraints);
            while (!fm.step());
            s.pop(1);
        }
        // we are done and soft_constraints has 
        // been updated with the max-sat assignment.

        return is_sat;
    }
};


