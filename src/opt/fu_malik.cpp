/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    fu_malik.cpp

Abstract:
    Fu & Malik built-in optimization method.
    Adapted from sample code in C.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-15

Notes:

--*/

#include "fu_malik.h"
#include "qfbv_tactic.h"
#include "tactic2solver.h"
#include "goal.h"
#include "probe.h"
#include "tactic.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"
#include "opt_context.h"

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

    class fu_malik : public maxsmt_solver_base {
        filter_model_converter& m_fm;
        expr_ref_vector m_aux_soft;
        expr_ref_vector m_aux;
        model_ref       m_model;

    public:
        fu_malik(maxsat_context& c, weights_t& ws, expr_ref_vector const& soft):
            maxsmt_solver_base(c, ws, soft),
            m_fm(c.fm()),
            m_aux_soft(soft),
            m_aux(m) 
        {
            m_upper = rational(m_aux_soft.size() + 1);
            m_lower.reset();
            m_assignment.resize(m_aux_soft.size(), false);
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

        typedef obj_hashtable<expr> expr_set;

        void set2vector(expr_set const& set, expr_ref_vector & es) const {
            es.reset();
            expr_set::iterator it = set.begin(), end = set.end();
            for (; it != end; ++it) {
                es.push_back(*it);
            }
        }

        void collect_statistics(statistics& st) const {
            st.update("opt-fm-num-steps", m_aux_soft.size() + 2 - m_upper.get_unsigned());
        }

        void set_union(expr_set const& set1, expr_set const& set2, expr_set & set) const {
            set.reset();
            expr_set::iterator it = set1.begin(), end = set1.end();
            for (; it != end; ++it) {
                set.insert(*it);
            }
            it = set2.begin();
            end = set2.end();
            for (; it != end; ++it) {
                set.insert(*it);
            }
        }

        lbool step() {
            IF_VERBOSE(1, verbose_stream() << "(opt.max_sat step " << m_aux_soft.size() + 2 - m_upper.get_unsigned() << ")\n";);
            expr_ref_vector assumptions(m), block_vars(m);
            for (unsigned i = 0; i < m_aux_soft.size(); ++i) {
                assumptions.push_back(m.mk_not(m_aux[i].get()));
            }
            lbool is_sat = s().check_sat(assumptions.size(), assumptions.c_ptr());
            if (is_sat != l_false) {
                return is_sat;
            }

            ptr_vector<expr> core;
            s().get_unsat_core(core);

            SASSERT(!core.empty());

            // Update soft-constraints and aux_vars
            for (unsigned i = 0; i < m_aux_soft.size(); ++i) {
                
                bool found = false;
                for (unsigned j = 0; !found && j < core.size(); ++j) {
                    found = assumptions[i].get() == core[j];
                }
                if (!found) {
                    continue;
                }
                app_ref block_var(m), tmp(m);
                block_var = m.mk_fresh_const("block_var", m.mk_bool_sort());
                m_aux[i] = m.mk_fresh_const("aux", m.mk_bool_sort());
                m_fm.insert(block_var->get_decl());
                m_fm.insert(to_app(m_aux[i].get())->get_decl());
                m_aux_soft[i] = m.mk_or(m_aux_soft[i].get(), block_var);
                block_vars.push_back(block_var);
                tmp = m.mk_or(m_aux_soft[i].get(), m_aux[i].get());
                s().assert_expr(tmp);
            }
            SASSERT (!block_vars.empty());
            assert_at_most_one(block_vars);
            IF_VERBOSE(1, verbose_stream() << "(opt.max_sat # of non-blocked soft constraints: " << m_aux_soft.size() - block_vars.size() << ")\n";);
            return l_false;
        }

        void assert_at_most_one(expr_ref_vector const& block_vars) {
            expr_ref has_one(m), has_zero(m), at_most_one(m);
            mk_at_most_one(block_vars.size(), block_vars.c_ptr(), has_one, has_zero);
            at_most_one = m.mk_or(has_one, has_zero);
            s().assert_expr(at_most_one);
        }

        void mk_at_most_one(unsigned n, expr* const * vars, expr_ref& has_one, expr_ref& has_zero) {
            SASSERT(n != 0);
            if (n == 1) {
                has_one = vars[0];
                has_zero = m.mk_not(vars[0]);
            }
            else {
                unsigned mid = n/2;
                expr_ref has_one1(m), has_one2(m), has_zero1(m), has_zero2(m);
                mk_at_most_one(mid,   vars,     has_one1, has_zero1);
                mk_at_most_one(n-mid, vars+mid, has_one2, has_zero2);
                has_one = m.mk_or(m.mk_and(has_one1, has_zero2), m.mk_and(has_one2, has_zero1));
                has_zero  = m.mk_and(has_zero1, has_zero2);
            }
        }
        

        // TBD: bug when cancel flag is set, fu_malik returns is_sat == l_true instead of l_undef
        virtual lbool operator()() {
            lbool is_sat = l_true;                
            if (m_aux_soft.empty()) {
                return is_sat;
            }
            solver::scoped_push _sp(s());
            expr_ref tmp(m);

            TRACE("opt",
                  tout << "soft constraints:\n";
                  for (unsigned i = 0; i < m_aux_soft.size(); ++i) {
                      tout << mk_pp(m_aux_soft[i].get(), m) << "\n";
                  });

            for (unsigned i = 0; i < m_aux_soft.size(); ++i) {
                m_aux.push_back(m.mk_fresh_const("p", m.mk_bool_sort()));
                m_fm.insert(to_app(m_aux.back())->get_decl());
                tmp = m.mk_or(m_aux_soft[i].get(), m_aux[i].get());
                s().assert_expr(tmp);
            }
            
            do {
                is_sat = step();
                --m_upper;
            }
            while (is_sat == l_false);
            
            if (is_sat == l_true) {
                // Get a list satisfying m_aux_soft
                s().get_model(m_model);
                m_lower = m_upper;
                m_assignment.reset();                    
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    expr_ref val(m);
                    VERIFY(m_model->eval(m_soft[i], val));
                    TRACE("opt", tout << val << "\n";);
                    m_assignment.push_back(m.is_true(val));                        
                }
                TRACE("opt", tout << "maxsat cost: " << m_upper << "\n";
                      model_smt2_pp(tout, m, *m_model, 0););
            }
            // We are done and soft_constraints has 
            // been updated with the max-sat assignment.            
            return is_sat;            
        }

        virtual void get_model(model_ref& mdl) {
            mdl = m_model.get();
        }

        virtual rational get_lower() const {
            return rational(m_aux_soft.size())-m_upper;
        }

        virtual rational get_upper() const {
            return rational(m_aux_soft.size())-m_lower;
        }
    };

    maxsmt_solver_base* mk_fu_malik(maxsat_context& c, weights_t & ws, expr_ref_vector const& soft) {
        return alloc(fu_malik, c, ws, soft);
    }

};

